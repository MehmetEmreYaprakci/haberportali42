"""Haber Radarı 42 v4.3 — Kararlı arayüz ve sunucu taraflı haber görselleri.

Kurulum: py -m pip install -r requirements.txt
Panel:   py -m streamlit run haber_radari.py
Tek sefer topla: py haber_radari.py --collect
"""

import calendar
from functools import lru_cache
import hashlib
import io
import socket
import ipaddress
import json
import shutil
import uuid
import re
import sqlite3
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

import feedparser
import requests
from PIL import Image, UnidentifiedImageError
import streamlit as st

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = APP_DIR / 'data'
IHA_INBOX_DIR = DATA_DIR / 'iha_gelen'
IHA_MEDIA_DIR = DATA_DIR / 'iha_medya'
IHA_ALLOWED_EXTENSIONS = {'.mp4', '.webm', '.mov', '.m4v'}
DB_PATH = DATA_DIR / 'haberler.db'
THUMB_DIR = DATA_DIR / 'kucuk_fotograflar'
THUMB_MAX_BYTES = 4_000_000
THUMB_RETRY_HOURS = 12
SOURCES_PATH = APP_DIR / 'sources.json'
VIDEO_SOURCES_PATH = APP_DIR / 'video_sources.json'
ISTANBUL = timezone(timedelta(hours=3))
INTERVAL_SECONDS = 300
VALID_GROUPS = {'Son Dakika', 'Konya', 'Konya Son Dakika', 'Türkiye',
                'Ekonomi', 'Tarım', 'Spor', 'Dünya', 'Teknoloji'}
HEADERS = {'User-Agent': 'Mozilla/5.0 (compatible; HaberRadari42/4.3; personal news reader)'}
# Yazılı haber RSS'indeki media:content alanları çoğu zaman habere ait olmayan
# tanıtım videoları da içerir. Doğrulamadan video havuzuna aktarma.
AUTO_IMPORT_RSS_VIDEOS = False

KONYA_KELIMELERI = [
    'Konya', 'Selçuklu', 'Meram', 'Karatay', 'Ahırlı', 'Akören', 'Akşehir',
    'Altınekin', 'Beyşehir', 'Bozkır', 'Cihanbeyli', 'Çeltik', 'Çumra',
    'Derbent', 'Derebucak', 'Doğanhisar', 'Emirgazi', 'Ereğli', 'Güneysınır',
    'Hadim', 'Halkapınar', 'Hüyük', 'Ilgın', 'Kadınhanı', 'Karapınar',
    'Kulu', 'Sarayönü', 'Seydişehir', 'Taşkent', 'Tuzlukçu', 'Yalıhüyük', 'Yunak',
]
EKONOMI_KELIMELERI = ['ekonomi', 'faiz', 'enflasyon', 'ihracat', 'döviz',
                      'borsa', 'tarım', 'çiftçi', 'traktör', 'üretim', 'yatırım']


def canonical_url(raw_url):
    try:
        parts = urlsplit(str(raw_url or '').strip())
        if parts.scheme.lower() not in ('http', 'https') or not parts.hostname:
            return None
        qs = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
              if not k.lower().startswith('utm_') and k.lower() not in ('fbclid', 'gclid')]
        return urlunsplit((parts.scheme.lower(), parts.netloc.lower(),
                           parts.path or '/', urlencode(qs), ''))
    except ValueError:
        return None


def image_url(raw, base):
    if not raw:
        return None
    url = canonical_url(urljoin(base, unescape(str(raw).strip())))
    if not url:
        return None
    path = urlsplit(url).path.lower()
    if path.endswith(('.svg', '.svgz', '.gif', '.mp4', '.webm', '.mp3', '.pdf')):
        return None
    return url


def is_safe_article_url(url):
    """Haber sayfası önizleme isteklerinde yerel/private IP adreslerini dışla."""
    try:
        parts = urlsplit(url)
        host = (parts.hostname or '').lower()
        if parts.scheme != 'https' or not host or host == 'localhost' or host.endswith('.local'):
            return False
        try:
            ip = ipaddress.ip_address(host)
            return ip.is_global
        except ValueError:
            return True
    except (ValueError, TypeError):
        return False


def load_sources():
    with SOURCES_PATH.open('r', encoding='utf-8') as handle:
        items = json.load(handle)
    if not isinstance(items, list):
        raise ValueError('sources.json bir JSON listesi olmalı')
    selected, names, urls = [], set(), set()
    for index, item in enumerate(items, 1):
        if not isinstance(item, dict):
            raise ValueError(f'Kaynak {index} nesne olmalı')
        if item.get('enabled', True) is False:
            continue
        name, url = str(item.get('name', '')).strip(), str(item.get('url', '')).strip()
        group = str(item.get('group', 'Türkiye')).strip()
        homepage = str(item.get('homepage', '')).strip()
        if not name or not canonical_url(url) or group not in VALID_GROUPS:
            raise ValueError(f'Kaynak {index}: ad, adres veya grup hatalı')
        if homepage and not canonical_url(homepage):
            raise ValueError(f'{name}: homepage adresi hatalı')
        if name in names or url in urls:
            raise ValueError(f'Tekrarlanan RSS kaynağı: {name} / {url}')
        selected.append({'name': name, 'url': url, 'group': group, 'homepage': homepage})
        names.add(name)
        urls.add(url)
    return selected


def load_video_sources():
    """YouTube kanal Atom akışları ve medya RSS kaynaklarını yükle."""
    with VIDEO_SOURCES_PATH.open('r', encoding='utf-8') as handle:
        items = json.load(handle)
    if not isinstance(items, list):
        raise ValueError('video_sources.json bir JSON listesi olmalı')
    selected, names, urls = [], set(), set()
    for index, item in enumerate(items, 1):
        if not isinstance(item, dict) or item.get('enabled', True) is False:
            continue
        name = str(item.get('name', '')).strip()
        url = canonical_url(item.get('url', ''))
        group = str(item.get('group', 'Türkiye')).strip()
        if not name or not url or group not in VALID_GROUPS:
            raise ValueError(f'Video kaynağı {index}: ad/adres/grup hatalı')
        if name in names or url in urls:
            raise ValueError(f'Tekrarlanan video kaynağı: {name}')
        selected.append({'name': name, 'url': url, 'group': group})
        names.add(name)
        urls.add(url)
    return selected


def tr_normalize(value):
    return str(value or '').casefold().translate(str.maketrans(
        {'ı': 'i', 'ğ': 'g', 'ü': 'u', 'ş': 's', 'ö': 'o', 'ç': 'c', '\u0307': ''}))


def has_keyword(text, keywords):
    norm = tr_normalize(text)
    return any(re.search(r'(?<!\w)' + re.escape(tr_normalize(k)) + r'(?!\w)', norm)
               for k in keywords)


def classify(title, summary, group):
    combined = f'{title} {summary}'
    if has_keyword(combined, KONYA_KELIMELERI) or group in ('Konya', 'Konya Son Dakika'):
        return 'Konya'
    if group in ('Tarım', 'Spor', 'Dünya', 'Teknoloji'):
        return group
    if group == 'Ekonomi' or has_keyword(combined, EKONOMI_KELIMELERI):
        return 'Ekonomi'
    return 'Türkiye'


def clean_text(value):
    return ' '.join(unescape(re.sub(r'<[^>]+>', ' ', str(value or ''))).split())


def as_iso(entry):
    parts = entry.get('published_parsed') or entry.get('updated_parsed')
    if not parts:
        return None
    try:
        return datetime.fromtimestamp(calendar.timegm(parts), timezone.utc).isoformat()
    except (ValueError, OverflowError, TypeError):
        return None


class HtmlImageParser(HTMLParser):
    """Haberin kendi sayfasındaki sosyal paylaşım görselini veya HTML img'sini bul."""
    def __init__(self):
        super().__init__()
        self.meta_images = []
        self.first_image = None
        self.feed_links = []

    def handle_starttag(self, tag, attributes):
        props = {k.lower(): v for k, v in attributes if k and v}
        if tag == 'meta':
            key = (props.get('property') or props.get('name') or '').lower()
            if key in ('og:image', 'og:image:url', 'twitter:image', 'twitter:image:src'):
                self.meta_images.append(props.get('content'))
        elif tag == 'img' and not self.first_image:
            self.first_image = props.get('src') or props.get('data-src')
        elif tag == 'link':
            rel = (props.get('rel') or '').lower()
            content_type = (props.get('type') or '').lower()
            if 'alternate' in rel and ('rss' in content_type or 'atom' in content_type):
                self.feed_links.append(props.get('href'))


def feed_image(entry, base):
    # RSS / Atom / Media RSS / enclosure / açıklamaya gömülü <img>.
    for key in ('media_thumbnail', 'media_content', 'enclosures', 'links'):
        for obj in entry.get(key, []) or []:
            if not isinstance(obj, dict):
                continue
            mime = (obj.get('type') or '').lower()
            if key in ('enclosures', 'links') and mime and not mime.startswith('image/'):
                continue
            if key == 'links' and obj.get('rel') != 'enclosure':
                continue
            if key == 'media_content' and mime and not mime.startswith('image/'):
                continue
            value = obj.get('url') or obj.get('href')
            url = image_url(value, base)
            if url:
                return url
    for key in ('image', 'image_url', 'thumbnail'):
        v = entry.get(key)
        value = (v.get('href') or v.get('url')) if isinstance(v, dict) else v
        url = image_url(value, base)
        if url:
            return url
    for key in ('summary', 'description'):
        html = entry.get(key, '')
        if '<img' in str(html).lower():
            parser = HtmlImageParser()
            parser.feed(str(html))
            url = image_url(parser.first_image, base)
            if url:
                return url
    for content in entry.get('content', []) or []:
        parser = HtmlImageParser()
        parser.feed(content.get('value', ''))
        url = image_url(parser.first_image, base)
        if url:
            return url
    return None


def discover_rss(homepage):
    """Sitenin HTML'inde yayıncı tarafından belirtilmiş RSS/Atom bağlantısını bul."""
    if not homepage or not is_safe_article_url(homepage):
        return None
    try:
        response = requests.get(homepage, timeout=(4, 7), headers=HEADERS)
        response.raise_for_status()
        parser = HtmlImageParser()
        parser.feed(response.text[:250_000])
        for link in parser.feed_links:
            found = canonical_url(urljoin(homepage, link))
            if found:
                return found
    except (requests.RequestException, ValueError):
        pass
    return None


def fetch_feed(source):
    """Önce resmî RSS bağlantısı; varsa başarısız olursa tanımlı yedeği dene."""
    name, group = source['name'], source['group']
    discovered = discover_rss(source.get('homepage')) if source.get('homepage') else None
    feeds = [(discovered, 'Yayıncı RSS')] if discovered else []
    if not discovered or discovered != source['url']:
        label = 'Google Haberler' if 'news.google.com/' in source['url'] else 'Yayıncı RSS'
        feeds.append((source['url'], label))
    last_error = None
    for url, method in feeds:
        try:
            response = requests.get(url, timeout=(5, 13), headers=HEADERS)
            response.raise_for_status()
            parsed = feedparser.parse(response.content)
            if not parsed.entries:
                raise ValueError('RSS boş, geçersiz veya ulaşılamıyor')
            records = []
            for entry in parsed.entries:
                title = clean_text(entry.get('title', ''))
                article_url = canonical_url(entry.get('link', ''))
                if not title or not article_url:
                    continue
                summary = clean_text(entry.get('summary', ''))[:1000]
                photo = feed_image(entry, article_url)
                video = video_from_feed_entry(entry, article_url) if AUTO_IMPORT_RSS_VIDEOS else None
                records.append((name, title, summary, article_url, classify(title, summary, group),
                                int(group in ('Son Dakika', 'Konya Son Dakika')),
                                as_iso(entry), photo, video))
            if not records:
                raise ValueError('Geçerli haber bağlantısı bulunamadı')
            return records, None, method, url
        except (requests.RequestException, ValueError, TypeError) as exc:
            last_error = str(exc)[:300]
    return [], last_error or 'RSS okunamadı', feeds[-1][1], feeds[-1][0]


def db():
    connection = sqlite3.connect(DB_PATH, timeout=20)
    connection.row_factory = sqlite3.Row
    connection.execute('PRAGMA busy_timeout = 20000')
    return connection


def ensure_column(conn, table, column, ddl):
    columns = {row[1] for row in conn.execute(f'PRAGMA table_info({table})')}
    if column not in columns:
        conn.execute(f'ALTER TABLE {table} ADD COLUMN {column} {ddl}')


def init_db():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    # Mevcut veritabanını ilk V4.3 başlangıcında bir defa güvenli şekilde yedekle.
    backup_path = DATA_DIR / 'haberler-v43-oncesi-yedek.db'
    if DB_PATH.exists() and not backup_path.exists():
        with sqlite3.connect(DB_PATH) as source, sqlite3.connect(backup_path) as target:
            source.backup(target)
    with db() as conn:
        conn.execute('''CREATE TABLE IF NOT EXISTS news (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            source TEXT NOT NULL, title TEXT NOT NULL, summary TEXT NOT NULL,
            url TEXT NOT NULL UNIQUE, category TEXT NOT NULL,
            is_breaking INTEGER NOT NULL DEFAULT 0, published_at TEXT,
            collected_at TEXT NOT NULL, is_read INTEGER NOT NULL DEFAULT 0,
            is_favorite INTEGER NOT NULL DEFAULT 0,
            image_url TEXT, image_checked_at TEXT
        )''')
        conn.execute('''CREATE TABLE IF NOT EXISTS source_status (
            name TEXT PRIMARY KEY, checked_at TEXT NOT NULL, error TEXT,
            added_count INTEGER NOT NULL DEFAULT 0, method TEXT, feed_url TEXT
        )''')
        conn.execute('CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY,value TEXT NOT NULL)')
        # V2'deki veritabanını ve favorileri silmeden görsel alanlarını ekle.
        ensure_column(conn, 'news', 'image_url', 'TEXT')
        ensure_column(conn, 'news', 'image_checked_at', 'TEXT')
        ensure_column(conn, 'news', 'thumbnail_checked_at', 'TEXT')
        ensure_column(conn, 'news', 'thumbnail_status', 'TEXT')
        ensure_column(conn, 'source_status', 'method', 'TEXT')
        ensure_column(conn, 'source_status', 'feed_url', 'TEXT')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_news_category ON news(category)')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_news_published ON news(published_at)')
        # V4: Eski haber tablosunu değiştirmeden bağımsız video arşivi açılır.
        conn.execute('''CREATE TABLE IF NOT EXISTS videos (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            source TEXT NOT NULL, title TEXT NOT NULL,
            summary TEXT NOT NULL DEFAULT '', article_url TEXT NOT NULL,
            video_url TEXT NOT NULL UNIQUE, category TEXT NOT NULL,
            published_at TEXT, collected_at TEXT NOT NULL,
            thumbnail_url TEXT, is_favorite INTEGER NOT NULL DEFAULT 0,
            is_watched INTEGER NOT NULL DEFAULT 0
        )''')
        conn.execute('''CREATE TABLE IF NOT EXISTS video_source_status (
            name TEXT PRIMARY KEY, checked_at TEXT NOT NULL, error TEXT,
            added_count INTEGER NOT NULL DEFAULT 0
        )''')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_videos_published ON videos(published_at)')
        # Önceki sürümde yazılı RSS akışından alınan videolar güvenilir biçimde
        # haberle eşleştirilemiyordu. Bunları SİLMEDEN karantinaya alıyoruz.
        ensure_column(conn, 'videos', 'origin', "TEXT NOT NULL DEFAULT 'legacy'")
        ensure_column(conn, 'videos', 'is_quarantined', 'INTEGER NOT NULL DEFAULT 0')
        ensure_column(conn, 'videos', 'validation_note', 'TEXT')
        ensure_column(conn, 'videos', 'iha_story_id', 'TEXT')
        ensure_column(conn, 'videos', 'rights_note', 'TEXT')
        conn.execute('''CREATE UNIQUE INDEX IF NOT EXISTS idx_iha_story_id
            ON videos(iha_story_id) WHERE origin='iha_manual' AND iha_story_id IS NOT NULL''')
        if SOURCES_PATH.exists():
            try:
                with SOURCES_PATH.open('r', encoding='utf-8') as reader:
                    news_source_names = [str(src.get('name', '')).strip()
                                         for src in json.load(reader) if src.get('name')]
            except (OSError, ValueError, TypeError):
                news_source_names = []
            if news_source_names:
                placeholders = ','.join('?' for _ in news_source_names)
                conn.execute(f'''UPDATE videos SET is_quarantined=1,
                    origin='news_rss', validation_note='Yazılı haber RSS videosu eşleştirilmedi'
                    WHERE source IN ({placeholders}) AND origin IN ('legacy','news_rss')''',
                    news_source_names)



# ------------------------------------------------------------------------
# HABER KÜÇÜK FOTOĞRAFLARI (V4.3)
# Doğrudan URL yerine yerel JPG baytları st.image ile görüntülenir.
# Bazı yayıncılar başka sitelerden resim açmayı (hotlink) engeller.
# ------------------------------------------------------------------------

@lru_cache(maxsize=1024)
def _public_image_hostname(host):
    if host in ('localhost',) or host.endswith(('.localhost', '.local', '.internal')):
        return False
    try:
        return ipaddress.ip_address(host).is_global
    except ValueError:
        try:
            addresses = socket.getaddrinfo(host, None, type=socket.SOCK_STREAM)
            return bool(addresses) and all(
                ipaddress.ip_address(address[4][0]).is_global for address in addresses
            )
        except (OSError, ValueError):
            return False


def safe_remote_image_url(raw_url):
    """Yerel ağ/loopback adreslerinden resim istemeyerek SSRF riskini azalt."""
    url = canonical_url(raw_url)
    if not url:
        return None
    host = (urlsplit(url).hostname or '').lower()
    return url if _public_image_hostname(host) else None


def cache_file_for_image(url):
    return THUMB_DIR / (hashlib.sha256(url.encode('utf-8')).hexdigest() + '.jpg')


def cached_image_bytes(url):
    path = cache_file_for_image(url)
    if path.exists() and path.stat().st_size > 0:
        try:
            # Varsa eski önizlemeyi kullan; sağlayıcı o anda erişilemez olabilir.
            return path.read_bytes()
        except OSError:
            return None
    return None


def _request_remote_image(url, referer):
    """Görseli sınırlandırılmış boyut ve yönlendirmelerle al."""
    current = url
    headers = dict(HEADERS)
    headers['Accept'] = 'image/avif,image/webp,image/png,image/jpeg,image/*;q=0.8'
    if referer and safe_remote_image_url(referer):
        headers['Referer'] = referer
    for _ in range(4):
        current = safe_remote_image_url(current)
        if not current:
            return None
        with requests.get(current, headers=headers, stream=True, allow_redirects=False,
                          timeout=(3, 6)) as response:
            if response.status_code in (301, 302, 303, 307, 308):
                dest = response.headers.get('Location')
                if not dest:
                    return None
                current = urljoin(current, dest)
                continue
            response.raise_for_status()
            if 'html' in response.headers.get('Content-Type', '').lower():
                return None
            length = response.headers.get('Content-Length')
            if length and int(length) > THUMB_MAX_BYTES:
                return None
            chunks, total = [], 0
            for chunk in response.iter_content(chunk_size=32768):
                total += len(chunk)
                if total > THUMB_MAX_BYTES:
                    return None
                chunks.append(chunk)
            return b''.join(chunks)
    return None


def fetch_preview_bytes(raw_url, referer=None):
    """Görüntüyü doğrula, küçült, JPEG olarak diske kaydet."""
    url = safe_remote_image_url(raw_url)
    if not url:
        return None
    cached = cached_image_bytes(url)
    if cached:
        return cached
    try:
        payload = _request_remote_image(url, referer)
        if not payload:
            return None
        with Image.open(io.BytesIO(payload)) as photo:
            if photo.width > 12000 or photo.height > 12000 or photo.width * photo.height > 24_000_000:
                return None
            photo.load()
            if photo.width < 60 or photo.height < 40:
                return None
            if photo.mode not in ('RGB', 'L'):
                # Saydam PNG'leri beyaz fon üzerinde JPEG yap.
                rgba = photo.convert('RGBA')
                canvas = Image.new('RGB', rgba.size, (255, 255, 255))
                canvas.paste(rgba, mask=rgba.getchannel('A'))
                photo = canvas
            else:
                photo = photo.convert('RGB')
            photo.thumbnail((360, 240))
            output = io.BytesIO()
            photo.save(output, format='JPEG', quality=78, optimize=True)
            rendered = output.getvalue()
        THUMB_DIR.mkdir(parents=True, exist_ok=True)
        target = cache_file_for_image(url)
        temp = target.with_suffix('.tmp')
        temp.write_bytes(rendered)
        temp.replace(target)
        return rendered
    except (requests.RequestException, OSError, ValueError, TypeError, UnidentifiedImageError,
            Image.DecompressionBombError):
        return None


def _recent_failed_preview(record):
    if record['thumbnail_status'] != 'failed' or not record['thumbnail_checked_at']:
        return False
    try:
        since = datetime.fromisoformat(record['thumbnail_checked_at'])
        return datetime.now(timezone.utc) - since < timedelta(hours=THUMB_RETRY_HOURS)
    except ValueError:
        return False


def _get_news_image_result(record, force=False):
    news_id = record['id']
    image_link = record['image_url']
    if image_link:
        cached = cached_image_bytes(image_link)
        if cached:
            return news_id, cached, image_link, 'ok'
    if not force and _recent_failed_preview(record):
        return news_id, None, image_link, 'failed'
    if image_link:
        photo = fetch_preview_bytes(image_link, record['url'])
        if photo:
            return news_id, photo, image_link, 'ok'
    # Önceki RSS görüntüsü yanlış veya hotlink engelli ise sayfa meta verisini tara.
    # Google Haberler yönlendirme sayfalarında bunu yapmıyoruz.
    fallback_link = get_article_photo(record['url'])
    if fallback_link and fallback_link != image_link:
        photo = fetch_preview_bytes(fallback_link, record['url'])
        if photo:
            return news_id, photo, fallback_link, 'ok'
    return news_id, None, image_link, 'failed'


def prepare_news_photos(records, force=False):
    """Sadece görünen sayfanın fotoğraflarını paralel olarak yerelleştir."""
    if not records:
        return {}
    results = {}
    with ThreadPoolExecutor(max_workers=6) as pool:
        jobs = [pool.submit(_get_news_image_result, dict(r), force) for r in records]
        for job in as_completed(jobs):
            try:
                record_id, data, final_url, status = job.result()
            except Exception:
                continue
            results[record_id] = data
            with db() as conn:
                conn.execute("UPDATE news SET image_url=COALESCE(?, image_url), "
                    "thumbnail_checked_at=?, thumbnail_status=? WHERE id=?",
                    (final_url, datetime.now(timezone.utc).isoformat(), status, record_id))
    return results


def prepare_video_thumbnails(records):
    images = {}
    candidates = [r for r in records if r['thumbnail_url']]
    with ThreadPoolExecutor(max_workers=6) as pool:
        jobs = {pool.submit(fetch_preview_bytes, r['thumbnail_url'], r['article_url']): r['id']
                for r in candidates}
        for future in as_completed(jobs):
            try:
                images[jobs[future]] = future.result()
            except Exception:
                images[jobs[future]] = None
    return images


def repair_existing_photos(limit=20):
    """Sorunlu URL'leri yeniden deneyip gerekiyorsa og:image ile değiştir."""
    with db() as conn:
        records = conn.execute("SELECT * FROM news ORDER BY "
            "CASE WHEN thumbnail_status='failed' THEN 0 ELSE 1 END, "
            "COALESCE(published_at,collected_at) DESC LIMIT ?", (limit,)).fetchall()
    results = prepare_news_photos(records, force=True)
    return sum(bool(x) for x in results.values())


def get_article_photo(article_url):
    """RSS fotoğraf vermiyorsa sayfanın og:image / twitter:image verisini dene."""
    if not is_safe_article_url(article_url) or 'news.google.com' in urlsplit(article_url).netloc:
        return None
    try:
        response = requests.get(article_url, timeout=(4, 8), headers=HEADERS, stream=True)
        response.raise_for_status()
        if 'html' not in response.headers.get('Content-Type', 'text/html').lower():
            return None
        pieces, used = [], 0
        for chunk in response.iter_content(chunk_size=32768):
            pieces.append(chunk)
            used += len(chunk)
            if used >= 500_000:
                break
        response.close()
        parser = HtmlImageParser()
        parser.feed(b''.join(pieces).decode(response.encoding or 'utf-8', errors='replace'))
        for raw in parser.meta_images:
            found = image_url(raw, article_url)
            if found:
                return found
    except (requests.RequestException, ValueError, UnicodeError):
        return None
    return None


def fill_missing_photos(limit=12):
    """İlk kez görülen fotoğrafsız haberlerde sınırlı sayıda önizleme denemesi."""
    with db() as conn:
        items = conn.execute('''SELECT id,url FROM news
            WHERE image_url IS NULL AND image_checked_at IS NULL
            ORDER BY COALESCE(published_at,collected_at) DESC LIMIT ?''', (limit,)).fetchall()
    if not items:
        return 0
    updated = 0
    checked_at = datetime.now(timezone.utc).isoformat()
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {pool.submit(get_article_photo, row['url']): row['id'] for row in items}
        for future in as_completed(futures):
            record_id = futures[future]
            try:
                photo = future.result()
            except Exception:
                photo = None
            with db() as conn:
                conn.execute('''UPDATE news SET image_url=COALESCE(image_url, ?),
                    image_checked_at=? WHERE id=?''', (photo, checked_at, record_id))
            updated += bool(photo)
    return updated


def collect_news(force=False):
    sources = load_sources()
    now = datetime.now(timezone.utc)
    with db() as conn:
        last = conn.execute("SELECT value FROM settings WHERE key='last_attempt'").fetchone()
        if last and not force:
            try:
                if (now - datetime.fromisoformat(last['value'])).total_seconds() < INTERVAL_SECONDS:
                    return 0, []
            except ValueError:
                pass
        conn.execute('''INSERT INTO settings(key,value) VALUES('last_attempt',?)
            ON CONFLICT(key) DO UPDATE SET value=excluded.value''', (now.isoformat(),))

    added_total, errors = 0, []
    with ThreadPoolExecutor(max_workers=5) as pool:
        jobs = {pool.submit(fetch_feed, s): s for s in sources}
        for future in as_completed(jobs):
            source = jobs[future]
            try:
                records, error, method, feed_url = future.result()
            except Exception as exc:
                records, error, method, feed_url = [], str(exc)[:300], 'Bilinmiyor', source['url']
            added = 0
            try:
                with db() as conn:
                    for name, title, summary, link, category, breaking, published, photo, video in records:
                        cursor = conn.execute('''INSERT OR IGNORE INTO news
                            (source,title,summary,url,category,is_breaking,published_at,collected_at,image_url)
                            VALUES (?,?,?,?,?,?,?,?,?)''',
                            (name, title, summary, link, category, breaking,
                             published, now.isoformat(), photo))
                        added += cursor.rowcount
                        if not cursor.rowcount and photo:
                            conn.execute('''UPDATE news SET image_url=COALESCE(image_url,?)
                                WHERE url=?''', (photo, link))
                        # Yazılı RSS'den otomatik video kaydetmek güvenilir değildir:
                        # haber ile görüntünün aynı olaya ait olduğu doğrulanmadı.
                        # Görüntülü haberler ayrı ve kimliği doğrulanmış video akışından gelir.
                    conn.execute('''INSERT INTO source_status
                        (name,checked_at,error,added_count,method,feed_url)
                        VALUES(?,?,?,?,?,?) ON CONFLICT(name) DO UPDATE SET
                        checked_at=excluded.checked_at,error=excluded.error,
                        added_count=excluded.added_count,method=excluded.method,
                        feed_url=excluded.feed_url''',
                        (source['name'], now.isoformat(), error, added, method, feed_url))
            except sqlite3.Error as exc:
                error = f'Veritabanı: {exc}'
            added_total += added
            if error:
                errors.append(f"{source['name']}: {error}")
    fill_missing_photos(limit=12)
    return added_total, errors


# ------------------------------------------------------------------------
# GÖRÜNTÜLÜ HABERLER: Video akışları yazılı haberlerden tamamen bağımsızdır.
# ------------------------------------------------------------------------


def youtube_video_id(raw_url):
    '''Yalnızca gerçek YouTube video bağlantılarının 11 karakterli kimliğini döndür.'''
    try:
        parts = urlsplit(str(raw_url or '').strip())
        host = (parts.hostname or '').lower()
        if host in ('youtube.com', 'www.youtube.com', 'm.youtube.com'):
            if parts.path == '/watch':
                candidate = dict(parse_qsl(parts.query)).get('v', '')
            elif parts.path.startswith(('/shorts/', '/live/', '/embed/')):
                candidate = parts.path.strip('/').split('/')[1]
            else:
                return None
        elif host in ('youtu.be', 'www.youtu.be'):
            candidate = parts.path.strip('/').split('/')[0]
        else:
            return None
        return candidate if re.fullmatch(r'[A-Za-z0-9_-]{11}', candidate) else None
    except (ValueError, IndexError):
        return None


def allowed_video_link(raw_url):
    '''YouTube ya da doğrudan HTTPS video akışı; yerel adresleri dışla.'''
    candidate = canonical_url(raw_url)
    if not candidate or not is_safe_article_url(candidate):
        return None
    video_id = youtube_video_id(candidate)
    if video_id:
        return f'https://www.youtube.com/watch?v={video_id}'
    if urlsplit(candidate).path.lower().endswith(('.mp4', '.webm', '.m4v', '.mov')):
        return candidate
    return None


def video_from_feed_entry(entry, base):
    '''YouTube/Atom veya RSS media:content + enclosure üzerinden video bul.'''
    link = allowed_video_link(entry.get('link', ''))
    if link:
        return link
    youtube_id = entry.get('yt_videoid')
    if youtube_id and re.fullmatch(r'[A-Za-z0-9_-]{11}', str(youtube_id)):
        return f'https://www.youtube.com/watch?v={youtube_id}'
    for key in ('media_content', 'enclosures', 'links'):
        for obj in entry.get(key, []) or []:
            mime = str(obj.get('type', '')).lower()
            if mime.startswith('video/'):
                url = allowed_video_link(urljoin(base, obj.get('url') or obj.get('href') or ''))
                if url:
                    return url
    media_players = entry.get('media_player', []) or []
    if isinstance(media_players, dict):
        media_players = [media_players]
    for obj in media_players:
        if isinstance(obj, dict):
            url = allowed_video_link(obj.get('url', ''))
            if url:
                return url
    return None


def fetch_video_feed(source):
    '''Video yayıncısının herkese açık Atom/RSS akışından metaveri al.'''
    response = requests.get(source['url'], timeout=(5, 15), headers=HEADERS)
    response.raise_for_status()
    parsed = feedparser.parse(response.content)
    if not parsed.entries:
        raise ValueError('Video RSS/Atom boş veya erişilemiyor')
    records = []
    for item in parsed.entries:
        title = clean_text(item.get('title', ''))
        article = canonical_url(item.get('link', ''))
        video = video_from_feed_entry(item, article or source['url'])
        if not video or not title:
            continue
        yt_id = youtube_video_id(video)
        feed_host = (urlsplit(source['url']).hostname or '').lower()
        is_yt_atom = feed_host in ('youtube.com', 'www.youtube.com') and (
            urlsplit(source['url']).path == '/feeds/videos.xml')
        if is_yt_atom:
            # Atom'un video kimliği ile haber bağlantısı AYNI video olmalı.
            # Aksi halde yanlış başlığa video iliştirilmesini engelle.
            declared_id = str(item.get('yt_videoid') or '').strip()
            if not yt_id or not declared_id or yt_id != declared_id:
                continue
            if article and youtube_video_id(article) != declared_id:
                continue
            feed_channel = dict(parse_qsl(urlsplit(source['url']).query)).get('channel_id')
            item_channel = str(item.get('yt_channelid') or '')
            if feed_channel and item_channel and feed_channel != item_channel:
                continue
            video = f'https://www.youtube.com/watch?v={declared_id}'
            article = video
        if not article:
            article = video
        summary = clean_text(item.get('summary', '') or item.get('media_description', ''))[:1200]
        thumbnail = (f'https://i.ytimg.com/vi/{yt_id}/hqdefault.jpg' if yt_id
                     else feed_image(item, article))
        records.append((source['name'], title, summary, article, video,
                        classify(title, summary, source['group']), as_iso(item), thumbnail))
    if not records:
        raise ValueError('Bu akışta oynatılabilir video bağlantısı bulunamadı')
    return records


def collect_videos(force=False):
    '''Video RSS adreslerini beş dakikada bir kontrol et; tekrar ekleme.'''
    sources = load_video_sources()
    now = datetime.now(timezone.utc)
    with db() as conn:
        last = conn.execute("SELECT value FROM settings WHERE key='last_video_attempt'").fetchone()
        if last and not force:
            try:
                if (now - datetime.fromisoformat(last['value'])).total_seconds() < INTERVAL_SECONDS:
                    return 0, []
            except ValueError:
                pass
        conn.execute('''INSERT INTO settings(key,value) VALUES('last_video_attempt',?)
            ON CONFLICT(key) DO UPDATE SET value=excluded.value''', (now.isoformat(),))
    errors, total = [], 0
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {pool.submit(fetch_video_feed, source): source for source in sources}
        for future in as_completed(futures):
            source = futures[future]
            error, records = None, []
            try:
                records = future.result()
            except (requests.RequestException, ValueError, TypeError) as exc:
                error = str(exc)[:300]
            except Exception as exc:
                error = f'Beklenmeyen kaynak hatası: {type(exc).__name__}'
            count = 0
            with db() as conn:
                try:
                    for row in records:
                        # Aynı video daha önce hatalı haber RSS'siyle eşleştirilmişse
                        # video kanalının doğru başlık/verileri ile ONAR.
                        # Favori ve izlendi bilgileri bu UPSERT'te değişmez.
                        old = conn.execute('SELECT id FROM videos WHERE video_url=?', (row[4],)).fetchone()
                        conn.execute('''INSERT INTO videos
                            (source,title,summary,article_url,video_url,category,published_at,collected_at,
                             thumbnail_url,origin,is_quarantined,validation_note)
                            VALUES(?,?,?,?,?,?,?,?,?,'video_feed',0,NULL)
                            ON CONFLICT(video_url) DO UPDATE SET
                                source=excluded.source,title=excluded.title,
                                summary=excluded.summary,article_url=excluded.article_url,
                                category=excluded.category,published_at=excluded.published_at,
                                thumbnail_url=excluded.thumbnail_url,origin='video_feed',
                                is_quarantined=0,validation_note=NULL''',
                            (*row[:7], now.isoformat(), row[7]))
                        count += int(old is None)
                    conn.execute('''INSERT INTO video_source_status
                        (name,checked_at,error,added_count) VALUES(?,?,?,?)
                        ON CONFLICT(name) DO UPDATE SET checked_at=excluded.checked_at,
                        error=excluded.error, added_count=excluded.added_count''',
                        (source['name'], now.isoformat(), error, count))
                except sqlite3.Error as exc:
                    error = f'Veritabanı: {exc}'
            total += count
            if error:
                errors.append(f"{source['name']}: {error}")
    return total, errors


def toggle_video_flag(video_id, field):
    if field not in ('is_favorite', 'is_watched'):
        return
    with db() as conn:
        conn.execute(f'UPDATE videos SET {field}=1-{field} WHERE id=?', (video_id,))


def add_manual_video(raw_url, title, source='Elle eklenen'):
    '''URL yapıştırarak tekil video ekle; telifli dosyaları indirmez.'''
    url = allowed_video_link(raw_url)
    title = clean_text(title)[:250]
    if not url or not title:
        raise ValueError('Geçerli bir YouTube/HTTPS video bağlantısı ve başlık gir.')
    youtube_id = youtube_video_id(url)
    thumbnail = f'https://i.ytimg.com/vi/{youtube_id}/hqdefault.jpg' if youtube_id else None
    now = datetime.now(timezone.utc).isoformat()
    with db() as conn:
        cursor = conn.execute('''INSERT OR IGNORE INTO videos
            (source,title,summary,article_url,video_url,category,published_at,collected_at,thumbnail_url,
             origin,is_quarantined)
            VALUES(?,?,?,?,?,?,?,?,?,'manual',0)''',
            (source, title, '', url, url, classify(title, '', 'Türkiye'),
             now, now, thumbnail))
    return cursor.rowcount > 0


def resolve_video_for_player(raw_url):
    """İHA dosyalarını taşınabilir göreli kayıtlarla bul; diğer URL'lere dokunma."""
    value = str(raw_url or '')
    if not value.startswith('iha-local:///'):
        return value
    filename = value.removeprefix('iha-local:///')
    if not re.fullmatch(r'[a-f0-9]{32}\.(mp4|webm|mov|m4v)', filename):
        return None
    target = IHA_MEDIA_DIR / filename
    return str(target) if target.is_file() else None


def get_iha_inbox_files():
    """Yalnızca uygulamanın iha_gelen klasöründeki video dosyalarını listele."""
    IHA_INBOX_DIR.mkdir(parents=True, exist_ok=True)
    return sorted([p for p in IHA_INBOX_DIR.iterdir()
                   if p.is_file() and not p.is_symlink() and
                   p.suffix.lower() in IHA_ALLOWED_EXTENSIONS],
                  key=lambda p: p.stat().st_mtime, reverse=True)


def import_iha_download(filename, story_id, title, summary='', article_url='', rights_note=''):
    """Kullanıcının İHA portalından kendisinin indirdiği dosyayı arşive al.

    Portalda oturum açmaz, CAPTCHA aşmaz, korumalı akış indirmez.
    Haber numarası zorunludur; başka video başlığıyla otomatik birleştirilmez.
    """
    story_id = str(story_id or '').strip()
    title = clean_text(title)[:250]
    summary = clean_text(summary)[:1500]
    rights_note = clean_text(rights_note)[:500]
    if not re.fullmatch(r'[\w.-]{2,100}', story_id, flags=re.UNICODE):
        raise ValueError('İHA haber numarası gerekli (2–100 karakter; harf, rakam, nokta, çizgi).')
    if not title:
        raise ValueError('Haber başlığı boş olamaz.')
    inbox = IHA_INBOX_DIR.resolve()
    target_source = (IHA_INBOX_DIR / str(filename)).resolve(strict=True)
    if target_source.parent != inbox or not target_source.is_file() or target_source.is_symlink():
        raise ValueError('Video yalnızca data/iha_gelen klasöründen alınabilir.')
    extension = target_source.suffix.lower()
    if extension not in IHA_ALLOWED_EXTENSIONS:
        raise ValueError('Yalnızca MP4, WEBM, MOV ve M4V videoları desteklenir.')
    if target_source.stat().st_size == 0:
        raise ValueError('Video dosyası boş.')
    article_url = str(article_url or '').strip()
    if article_url:
        checked = canonical_url(article_url)
        host = (urlsplit(checked).hostname or '') if checked else ''
        if not checked or not is_safe_article_url(checked) or not (host == 'iha.com.tr' or host.endswith('.iha.com.tr')):
            raise ValueError('Kaynak bağlantısı yalnızca İHA alan adındaki HTTPS sayfası olmalı.')
        article_url = checked
    else:
        article_url = 'https://abone.iha.com.tr/'
    with db() as conn:
        existing = conn.execute("""SELECT id FROM videos
            WHERE origin='iha_manual' AND iha_story_id=?""", (story_id,)).fetchone()
        if existing:
            raise ValueError('Bu İHA haber numarası zaten kayıtlı. Yanlış eşleşmeyi önlemek için tekrar eklenmedi.')
    IHA_MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    media_name = uuid.uuid4().hex + extension
    saved_path = IHA_MEDIA_DIR / media_name
    now = datetime.now(timezone.utc).isoformat()
    try:
        with target_source.open('rb') as reader, saved_path.open('xb') as writer:
            shutil.copyfileobj(reader, writer, length=1024 * 1024)
        with db() as conn:
            conn.execute("""INSERT INTO videos
                (source,title,summary,article_url,video_url,category,published_at,collected_at,
                 thumbnail_url,origin,is_quarantined,validation_note,iha_story_id,rights_note)
                VALUES (?,?,?,?,?,?,?,?,?,'iha_manual',0,NULL,?,?)""",
                ('İHA Abonelik', title, summary, article_url, 'iha-local:///' + media_name,
                 classify(title, summary, 'Türkiye'), now, now, None, story_id, rights_note))
    except Exception:
        saved_path.unlink(missing_ok=True)
        raise
    return saved_path


def render_iha_subscription_panel():
    st.subheader('🏢 İHA Abonelik — Görüntü Arşivi')
    st.info('Bu sürüm İHA abonelik hesabına otomatik giriş yapmaz. İHA panelinden aboneliğin '
            'kapsamında indirdiğin videoları, kendi bilgisayarındaki haber havuzuna ekler.')
    st.link_button('İHA abone panelini aç ↗', 'https://abone.iha.com.tr/', use_container_width=False)
    IHA_INBOX_DIR.mkdir(parents=True, exist_ok=True)
    st.markdown('**1.** İHA panelinde görüntülü haberi ve haber numarasını kontrol et. '
                '**2.** Aboneliğinin izin verdiği video dosyasını aşağıdaki klasöre indir veya kopyala. '
                '**3.** Başlığı, haber numarasını ve dosyayı eşleştirip arşive ekle.')
    st.code(str(IHA_INBOX_DIR), language=None)
    files = get_iha_inbox_files()
    with st.form('iha_import_form', clear_on_submit=False):
        selected = st.selectbox('İndirilen video dosyası',
            options=[p.name for p in files] if files else ['— Dosya bulunamadı —'])
        story_id = st.text_input('İHA haber numarası (zorunlu)', placeholder='Abone panelindeki haber numarası')
        title = st.text_input('İHA haber başlığı (zorunlu)')
        summary = st.text_area('Haber özeti / görüntü bilgileri (isteğe bağlı)')
        article = st.text_input('İHA panelindeki habere ait HTTPS bağlantısı (isteğe bağlı)')
        rights = st.text_input('Kullanım notu (isteğe bağlı)',
                               placeholder='Yalnızca mevcut abonelik yetkileri kapsamında')
        acknowledged = st.checkbox('Haber numarasının, başlığın ve video dosyasının aynı habere ait olduğunu kontrol ettim.')
        submit = st.form_submit_button('Görüntüyü İHA arşivine ekle', use_container_width=True)
    if submit:
        if not files:
            st.error('Önce data/iha_gelen klasörüne İHA portalından indirilen bir video kopyala.')
        elif not acknowledged:
            st.error('Kaydı eklemek için haber/video eşleşmesini doğrulamalısın.')
        else:
            try:
                result = import_iha_download(selected, story_id, title, summary, article, rights)
                st.success(f'İHA haberi arşive eklendi: {result.name}. Görüntülü Haberler sekmesinden izleyebilirsin.')
            except (ValueError, OSError, sqlite3.Error) as exc:
                st.error(str(exc))
    st.divider()
    with db() as conn:
        items = conn.execute("""SELECT iha_story_id,title,category,collected_at,rights_note FROM videos
            WHERE origin='iha_manual' ORDER BY id DESC LIMIT 40""").fetchall()
    st.markdown(f'**İHA abonelik arşivi — {len(items)} son kayıt**')
    if not items:
        st.caption('Henüz İHA abonelik videosu eklenmedi.')
    else:
        for item in items:
            st.caption(f"{item['iha_story_id']} · {item['title']} · {item['category']} · {time_tr(item['collected_at'])}")
    st.caption('Otomatik İHA video akışı için İHA’dan aboneliğine tanımlı resmî API, XML, RSS veya dosya aktarım yöntemi '
               've kullanım koşulları alınmalı. Şifre ve güvenlik kodunu bu uygulamaya yazma.')


def toggle_flag(news_id, field):
    if field not in ('is_read', 'is_favorite'):
        return
    with db() as conn:
        conn.execute(f'UPDATE news SET {field}=1-{field} WHERE id=?', (news_id,))


def time_tr(value):
    if not value:
        return 'Yayın tarihi belirtilmemiş'
    try:
        return datetime.fromisoformat(value).astimezone(ISTANBUL).strftime('%d.%m.%Y %H:%M')
    except ValueError:
        return 'Yayın tarihi belirtilmemiş'


def render_panel(category, term, source_filter, favorites_only, unread_only):
    try:
        _, errors = collect_news()
    except (requests.RequestException, sqlite3.Error) as exc:
        st.error(f'Toplama hatası: {exc}')
        errors = []

    sources = load_sources()
    with db() as conn:
        metrics = conn.execute('''SELECT COUNT(*) AS total,
            SUM(CASE WHEN category='Konya' THEN 1 ELSE 0 END) AS konya,
            SUM(CASE WHEN is_read=0 THEN 1 ELSE 0 END) AS unread,
            SUM(CASE WHEN thumbnail_status='ok' THEN 1 ELSE 0 END) AS pictured
            FROM news''').fetchone()
        status = {r['name']: r for r in conn.execute('SELECT * FROM source_status')}

    a, b, c, d = st.columns(4)
    a.metric('Toplam haber', metrics['total'])
    b.metric('Konya haberleri', metrics['konya'] or 0)
    c.metric('Okunmamış', metrics['unread'] or 0)
    d.metric('Fotoğrafı hazır', metrics['pictured'] or 0)

    with st.expander(f'📡 RSS kaynaklarının durumu ({len(sources)} etkin kaynak)'):
        for source in sources:
            name = source['name']
            s = status.get(name)
            if not s:
                st.caption(f'⚪ {name} — henüz kontrol edilmedi')
            elif s['error']:
                st.warning(f"{name}: {s['error']}")
            else:
                st.caption(f"✅ {name} — {s['method']} · {time_tr(s['checked_at'])}")
        st.caption('Google Haberler aktarımları ilgili sitenin kendi RSS akışı değildir.')
        st.caption('Kaynaklar sources.json dosyasından değiştirilebilir.')
    if errors:
        st.info('Bazı kaynaklara erişilemedi; ayrıntılar Kaynakların Durumu bölümünde.')

    clauses, args = [], []
    if category == 'Son Dakika':
        clauses.append('is_breaking=1')
    elif category != 'Tümü':
        clauses.append('category=?')
        args.append(category)
    if source_filter != 'Tüm kaynaklar':
        clauses.append('source=?')
        args.append(source_filter)
    if favorites_only:
        clauses.append('is_favorite=1')
    if unread_only:
        clauses.append('is_read=0')
    where = ' WHERE ' + ' AND '.join(clauses) if clauses else ''
    with db() as conn:
        rows = conn.execute('SELECT * FROM news' + where +
                            ' ORDER BY COALESCE(published_at,collected_at) DESC LIMIT 1500', args).fetchall()
    if term.strip():
        needle = tr_normalize(term.strip())
        rows = [r for r in rows if needle in tr_normalize(r['title'] + ' ' + r['summary'])]

    # Her defasında 80 dinamik HTML kartı üretmek yerine 16 haberlik sayfalar.
    per_page = 16
    total_pages = max(1, (len(rows) + per_page - 1) // per_page)
    st.caption(f'{len(rows)} haber bulundu · sayfa başına {per_page} haber.')
    if not rows:
        st.info('Henüz bu filtreye uygun haber bulunamadı.')
        return
    if total_pages > 1:
        page = st.selectbox('Sayfa', list(range(1, total_pages + 1)),
                            format_func=lambda v: f'{v} / {total_pages}',
                            key='news_page_select')
    else:
        page = 1
    current_rows = rows[(page - 1) * per_page: page * per_page]
    with st.spinner('Haberlerin küçük fotoğrafları hazırlanıyor...'):
        thumbs = prepare_news_photos(current_rows)

    for item in current_rows:
        with st.container(border=True):
            photo_col, content_col = st.columns([1.0, 4.8], gap='medium')
            with photo_col:
                preview = thumbs.get(item['id'])
                if preview:
                    # Dosya baytları Streamlit üzerinden servis edilir, site hotlink gerekmez.
                    st.image(preview, use_container_width=True)
                else:
                    st.caption('📰 Fotoğraf yok')
            with content_col:
                if item['is_breaking']:
                    st.caption('🚨 SON DAKİKA')
                st.markdown(f"**{item['title']}**")
                st.caption(f"{item['source']} · {item['category']} · {time_tr(item['published_at'])}")
                if item['summary']:
                    st.write(item['summary'][:220])
                action1, action2, action3 = st.columns([1, 1, 1])
                with action1:
                    st.link_button('Haberi aç ↗', item['url'], use_container_width=True)
                with action2:
                    label = '★ Kaydedildi' if item['is_favorite'] else '☆ Kaydet'
                    if st.button(label, key=f"fav_{item['id']}", use_container_width=True):
                        toggle_flag(item['id'], 'is_favorite')
                        st.rerun()
                with action3:
                    label = 'Okunmadı yap' if item['is_read'] else 'Okundu yap'
                    if st.button(label, key=f"read_{item['id']}", use_container_width=True):
                        toggle_flag(item['id'], 'is_read')
                        st.rerun()


# Stabilite: Otomatik fragment yeniden çizimi devre dışıdır.
# RSS toplama, normal panel yenilemelerinde 5 dakika aralığıyla kontrol edilir.
def live_panel(category, term, source_filter, favorites_only, unread_only):
    render_panel(category, term, source_filter, favorites_only, unread_only)


def render_video_panel(category, term, source_filter, favorites_only, unseen_only):
    try:
        _, failures = collect_videos()
    except (requests.RequestException, sqlite3.Error, ValueError, FileNotFoundError) as exc:
        failures = [str(exc)]
    sources = load_video_sources()
    with db() as conn:
        stats = conn.execute('''SELECT COUNT(*) AS total,
            SUM(CASE WHEN category='Konya' THEN 1 ELSE 0 END) AS konya,
            SUM(CASE WHEN is_watched=0 THEN 1 ELSE 0 END) AS unseen,
            SUM(CASE WHEN is_favorite=1 THEN 1 ELSE 0 END) AS favs
            FROM videos WHERE is_quarantined=0''').fetchone()
        suspect = conn.execute('SELECT COUNT(*) FROM videos WHERE is_quarantined=1').fetchone()[0]
        status = {row['name']: row for row in conn.execute('SELECT * FROM video_source_status')}
    st.subheader('🎬 Görüntülü Haberler')
    st.caption('Doğrulanabilir video kaynakları · yazılı RSS içindeki rastgele medya bağlantıları kullanılmaz.')
    a,b,c,d=st.columns(4)
    a.metric('Toplam video', stats['total'] or 0)
    b.metric('Konya ile ilgili', stats['konya'] or 0)
    c.metric('İzlenmemiş', stats['unseen'] or 0)
    d.metric('Favoriler', stats['favs'] or 0)
    if suspect:
        st.warning(f'{suspect} eski görüntülü haber kaydı güvenilir eşleştirme içermediğinden gizlendi. '
                   'Bu kayıtlar ve favorileri silinmedi; yalnızca kontrol için ayrıldı.')
        with st.expander('⚠️ Eşleştirmesi şüpheli eski kayıtları incele'):
            with db() as conn:
                questionable = conn.execute('''SELECT source,title,article_url,video_url
                    FROM videos WHERE is_quarantined=1 ORDER BY id DESC LIMIT 30''').fetchall()
            for q in questionable:
                st.caption(f"{q['source']} — {q['title'][:100]}")
                st.caption(f"Haber: {q['article_url']} · Video: {q['video_url']}")
            st.info('Kayıtlar silinmez. Video RSS kanalından doğrulanmış aynı video gelirse '
                    'doğru başlıkla güncellenip tekrar görünür.')
    with st.expander(f'📺 Video kaynaklarının durumu ({len(sources)} kaynak)'):
        for source in sources:
            info = status.get(source['name'])
            if not info:
                st.caption(f"⚪ {source['name']} — henüz kontrol edilmedi")
            elif info['error']:
                st.warning(f"{source['name']}: {info['error']}")
            else:
                st.caption(f"✅ {source['name']} · {time_tr(info['checked_at'])}")
    if failures:
        st.info('Bazı video akışlarına ulaşılamadı; diğer kaynaklar çalışmaya devam eder.')
    filters, args = ['is_quarantined=0'], []
    if category != 'Tümü':
        filters.append('category=?')
        args.append(category)
    if source_filter != 'Tüm video kaynakları':
        filters.append('source=?')
        args.append(source_filter)
    if favorites_only:
        filters.append('is_favorite=1')
    if unseen_only:
        filters.append('is_watched=0')
    clause = (' WHERE ' + ' AND '.join(filters)) if filters else ''
    with db() as conn:
        results = conn.execute('SELECT * FROM videos' + clause +
            ' ORDER BY COALESCE(published_at,collected_at) DESC LIMIT 800', args).fetchall()
    if term.strip():
        needle = tr_normalize(term.strip())
        results = [item for item in results
                   if needle in tr_normalize(item['title'] + ' ' + item['summary'])]
    st.caption(f'{len(results)} görüntülü haber bulundu · ilk 24 kayıt gösterilir.')
    if not results:
        st.info('Görüntülü haber bulunamadı. Soldaki “Videoları şimdi çek” düğmesini dene; kaynakları da kontrol et.')
        return
    visible_videos = results[:24]
    video_images = prepare_video_thumbnails(visible_videos)
    for item in visible_videos:
        with st.container(border=True):
            thumb, details = st.columns([1.2,4.5],gap='medium')
            with thumb:
                if video_images.get(item['id']):
                    st.image(video_images[item['id']], use_container_width=True)
                else:
                    st.caption('🎥 Önizleme yok')
            with details:
                st.markdown(f"**{item['title']}**")
                st.caption(f"{item['source']} · {item['category']} · {time_tr(item['published_at'])}")
                if item['summary']:
                    st.write(item['summary'][:230])
                col1,col2,col3,col4 = st.columns([1.2,1.0,1.0,1.0])
                with col1:
                    opened = st.session_state.get('open_video_id') == item['id']
                    if st.button('Kapat' if opened else '▶ İzle', key=f"vshow_{item['id']}",
                                 use_container_width=True):
                        st.session_state['open_video_id'] = None if opened else item['id']
                        if not opened and not item['is_watched']:
                            with db() as conn:
                                conn.execute('UPDATE videos SET is_watched=1 WHERE id=?', (item['id'],))
                        st.rerun()
                with col2:
                    st.link_button('Kaynağı aç ↗', item['article_url'], use_container_width=True)
                with col3:
                    label = '★ Kayıtlı' if item['is_favorite'] else '☆ Kaydet'
                    if st.button(label, key=f"vfav_{item['id']}", use_container_width=True):
                        toggle_video_flag(item['id'],'is_favorite')
                        st.rerun()
                with col4:
                    label = 'İzlenmedi' if item['is_watched'] else 'İzlendi'
                    if st.button(label, key=f"vwatch_{item['id']}", use_container_width=True):
                        toggle_video_flag(item['id'],'is_watched')
                        st.rerun()
            if st.session_state.get('open_video_id') == item['id']:
                try:
                    video_path = resolve_video_for_player(item['video_url'])
                    if video_path:
                        st.video(video_path)
                        st.caption('İHA abonelik videosu ise yalnızca bu bilgisayarda arşivlenen dosya oynatılır.')
                    else:
                        st.warning('Yerel video dosyası bulunamadı. data/iha_medya klasörünü kontrol et.')
                except Exception:
                    st.warning('Bu video panel içinde açılamadı. “Kaynağı aç” bağlantısını kullan.')


def live_video_panel(category, term, source_filter, favorites_only, unseen_only):
    render_video_panel(category, term, source_filter, favorites_only, unseen_only)


def main():
    st.set_page_config(page_title='Haber Radarı 42', page_icon='📡', layout='wide')
    st.title('📡 HABER RADARI 42')
    st.caption('Kişisel haber merkezi · yazılı ve görüntülü haberler · Konya odaklı')
    section = st.radio('Bölüm', ['📰 Yazılı Haberler', '🎬 Görüntülü Haberler', '🏢 İHA Abonelik'], horizontal=True)
    if section == '📰 Yazılı Haberler':
        sources = load_sources()
        with st.sidebar:
            st.header('📰 Yazılı Haber Filtresi')
            category = st.selectbox('Kategori', ['Tümü','Konya','Son Dakika','Türkiye',
                'Ekonomi','Tarım','Spor','Dünya','Teknoloji'])
            term = st.text_input('Kelime ara', placeholder='Konya, çiftçi, belediye...')
            source_filter = st.selectbox('Haber kaynağı',
                ['Tüm kaynaklar'] + [s['name'] for s in sources])
            favorites_only = st.checkbox('Yalnızca favoriler')
            unread_only = st.checkbox('Yalnızca okunmamışlar')
            st.divider()
            if st.button('Şimdi haberleri çek',use_container_width=True):
                with st.spinner('RSS kaynakları kontrol ediliyor...'):
                    added, failures = collect_news(force=True)
                st.success(f'{added} yeni haber eklendi.')
                if failures:
                    st.warning(f'{len(failures)} kaynağın akışına erişilemedi.')
            if st.button('Kırık fotoğrafları onar (20)',use_container_width=True):
                with st.spinner('Haber fotoğrafları kontrol ediliyor...'):
                    found = repair_existing_photos(limit=20)
                st.success(f'{found} haber için kullanılabilir küçük fotoğraf hazırlandı.')
        live_panel(category, term, source_filter, favorites_only, unread_only)
    elif section == '🎬 Görüntülü Haberler':
        sources = load_video_sources()
        with st.sidebar:
            st.header('🎬 Görüntülü Haber Filtresi')
            category = st.selectbox('Kategori', ['Tümü','Konya','Türkiye','Ekonomi',
                                                'Tarım','Spor','Dünya','Teknoloji'])
            term = st.text_input('Videolarda ara', placeholder='Konya, kaza, tarım...')
            with db() as conn:
                local_video_sources = [row['source'] for row in conn.execute(
                    'SELECT DISTINCT source FROM videos ORDER BY source')]
            choices = sorted(set(local_video_sources + [s['name'] for s in sources] + ['Elle eklenen']))
            source_filter = st.selectbox('Video kaynağı',
                ['Tüm video kaynakları'] + choices)
            favorites_only = st.checkbox('Yalnızca favoriler')
            unseen_only = st.checkbox('Yalnızca izlenmemişler')
            st.divider()
            if st.button('Videoları şimdi çek',use_container_width=True):
                with st.spinner('Video akışları kontrol ediliyor...'):
                    added, failures = collect_videos(force=True)
                st.success(f'{added} yeni video eklendi.')
                if failures:
                    st.warning(f'{len(failures)} video kaynağına erişilemedi.')
            with st.expander('➕ Video bağlantısını elle ekle'):
                manual_title=st.text_input('Başlık',key='manual_video_title')
                manual_url=st.text_input('YouTube veya HTTPS video adresi',key='manual_video_url')
                if st.button('Videoyu listeye ekle',use_container_width=True):
                    try:
                        if add_manual_video(manual_url,manual_title):
                            st.success('Video arşive kaydedildi.')
                            st.rerun()
                        else:
                            st.info('Video zaten arşivde.')
                    except ValueError as exc:
                        st.error(str(exc))
            st.caption('Ek video kanalları video_sources.json dosyasına yazılabilir.')
            st.link_button('İHA abonelik video portalını aç ↗', 'https://www.ihavideo.com.tr/', use_container_width=True)
            st.caption('İHA abonelik hesabı bu uygulamaya bağlı değildir. Portal ayrı açılır.')
        live_video_panel(category, term, source_filter, favorites_only, unseen_only)
    else:
        render_iha_subscription_panel()


if __name__ == '__main__':
    init_db()
    if '--collect' in sys.argv:
        news_added, news_errors = collect_news(force=True)
        video_added, video_errors = collect_videos(force=True)
        print(f'Yeni haber: {news_added}; yeni video: {video_added}')
        for msg in news_errors+video_errors:
            print('UYARI:',msg)
    else:
        try:
            main()
        except (ValueError, FileNotFoundError, json.JSONDecodeError) as exc:
            st.error(f'Kaynak yapılandırması hatası: {exc}')
