# Standard library imports
import os
import sys
import zipfile
import urllib.request
import shutil
import platform
import glob
import re
import time
import hashlib
import threading
import concurrent.futures
import json
import logging
import tempfile
import zlib
import fnmatch
import traceback
import psutil
import resource
from queue import Queue
from pathlib import Path
from tqdm import tqdm
from functools import lru_cache
from typing import Dict, List, Optional, Set, Tuple, Union, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
import struct
from concurrent.futures import ThreadPoolExecutor
import unittest
import signal
from contextlib import contextmanager

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Add FailureReport class definition before other classes
@dataclass
class FailureReport:
    """Track and report failures during operations"""
    errors: List[Dict[str, Any]] = field(default_factory=list)
    warnings: List[Dict[str, Any]] = field(default_factory=list)

    def add_error(self, file: str, message: str, **kwargs):
        self.errors.append({
            'file': file,
            'message': message,
            'timestamp': datetime.now().isoformat(),
            **kwargs
        })

    def add_warning(self, file: str, message: str, **kwargs):
        self.warnings.append({
            'file': file,
            'message': message,
            'timestamp': datetime.now().isoformat(),
            **kwargs
        })

    def get_report(self) -> Dict[str, Any]:
        return {
            'errors': self.errors,
            'warnings': self.warnings,
            'total_errors': len(self.errors),
            'total_warnings': len(self.warnings)
        }

class ColorOutput:
    """Enhanced color output handling with structured logging integration"""
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

    _enabled: bool = True
    _log_level: int = logging.INFO

    @classmethod
    def configure(cls, enable_color: bool = True, log_level: int = logging.INFO) -> None:
        """Configure color output and logging settings"""
        cls._enabled = enable_color
        cls._log_level = log_level
        logger.setLevel(log_level)

    @classmethod
    def _format_message(cls, level: str, message: str) -> str:
        """Format message with color if enabled"""
        if not cls._enabled:
            return f"[{level}] {message}"

        color = {
            'INFO': cls.BLUE,
            'SUCCESS': cls.GREEN,
            'WARNING': cls.YELLOW,
            'ERROR': cls.RED,
            'DEBUG': cls.CYAN
        }.get(level, '')

        return f"{color}[{level}]{cls.ENDC} {message}"

    @classmethod
    def log(cls, level: str, message: str) -> None:
        """Enhanced logging with color support and structured output"""
        formatted = cls._format_message(level, message)
        print(formatted)

        # Map to logging levels
        log_level = {
            'INFO': logging.INFO,
            'SUCCESS': logging.INFO,
            'WARNING': logging.WARNING,
            'ERROR': logging.ERROR,
            'DEBUG': logging.DEBUG
        }.get(level, logging.INFO)

        logger.log(log_level, message)

    @classmethod
    def print_info(cls, message: str) -> None:
        cls.log('INFO', message)

    @classmethod
    def print_success(cls, message: str) -> None:
        cls.log('SUCCESS', message)

    @classmethod
    def print_warning(cls, message: str) -> None:
        cls.log('WARNING', message)

    @classmethod
    def print_error(cls, message: str) -> None:
        cls.log('ERROR', message)

    @classmethod
    def print_debug(cls, message: str) -> None:
        if os.environ.get('DEBUG', '0') == '1':
            cls.log('DEBUG', message)

# Type aliases for better code readability
FilePath = Union[str, Path]
UrlType = str
FileList = List[str]
PathMapping = Dict[str, str]

# Add timeout handler
class TimeoutException(Exception):
    pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise TimeoutException("Timed out!")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)

# Add memory monitoring
class MemoryMonitor:
    """Monitor memory usage during operations"""
    @staticmethod
    def get_memory_usage() -> float:
        process = psutil.Process()
        return process.memory_info().rss / 1024 / 1024  # MB

    @staticmethod
    def check_memory_limit(limit_mb: float = 1024) -> bool:
        current_usage = MemoryMonitor.get_memory_usage()
        return current_usage < limit_mb

# Add file system checks
class FileSystemChecker:
    """Check file system permissions and space"""
    @staticmethod
    def check_permissions(path: str) -> bool:
        try:
            if os.path.exists(path):
                # Check read permission
                if not os.access(path, os.R_OK):
                    raise PermissionError(f"No read permission for {path}")
                # Check write permission for directories
                if os.path.isdir(path) and not os.access(path, os.W_OK):
                    raise PermissionError(f"No write permission for {path}")
            else:
                # Check if parent directory is writable
                parent = os.path.dirname(path)
                if not os.access(parent, os.W_OK):
                    raise PermissionError(f"No write permission for parent directory {parent}")
            return True
        except Exception as e:
            ColorOutput.print_error(f"Permission check failed: {e}")
            return False

    @staticmethod
    def check_disk_space(path: str, required_bytes: int) -> bool:
        try:
            total, used, free = shutil.disk_usage(os.path.dirname(path))
            if free < required_bytes:
                raise OSError(f"Insufficient disk space. Required: {required_bytes/1024/1024:.2f}MB, "
                              f"Available: {free/1024/1024:.2f}MB")
            return True
        except Exception as e:
            ColorOutput.print_error(f"Disk space check failed: {e}")
            return False


@dataclass
class CacheEntry:
    """Data class for cache entries with TTL support"""
    path: str
    timestamp: float
    ttl: int = 3600  # Default TTL: 1 hour

    @property
    def is_expired(self) -> bool:
        return time.time() - self.timestamp > self.ttl

class CacheManager:
    """Enhanced cache management with TTL support and cleanup"""
    def __init__(self, cache_dir: Optional[str] = None, default_ttl: int = 3600):
        self.cache_dir = cache_dir or os.path.join(os.path.dirname(os.path.abspath(__file__)), ".download_cache")
        self.default_ttl = default_ttl
        self.cache: Dict[str, CacheEntry] = {}
        self.lock = threading.Lock()

        # Create cache directory if it doesn't exist
        os.makedirs(self.cache_dir, exist_ok=True)

        # Load existing cache entries
        self._load_cache()

        # Start cleanup thread
        self._start_cleanup_thread()

    def _load_cache(self) -> None:
        """Load existing cache entries from disk"""
        try:
            cache_index = os.path.join(self.cache_dir, "cache_index.json")
            if os.path.exists(cache_index):
                with open(cache_index, 'r') as f:
                    data = json.load(f)
                    for url, entry in data.items():
                        self.cache[url] = CacheEntry(**entry)
        except Exception as e:
            ColorOutput.print_warning(f"Error loading cache index: {e}")

    def _save_cache(self) -> None:
        """Save cache index to disk"""
        try:
            cache_index = os.path.join(self.cache_dir, "cache_index.json")
            with open(cache_index, 'w') as f:
                data = {url: {"path": entry.path, "timestamp": entry.timestamp, "ttl": entry.ttl}
                       for url, entry in self.cache.items()}
                json.dump(data, f)
        except Exception as e:
            ColorOutput.print_warning(f"Error saving cache index: {e}")

    def _start_cleanup_thread(self) -> None:
        """Start background thread for cache cleanup"""
        def cleanup():
            while True:
                self.cleanup_expired()
                time.sleep(3600)  # Clean up every hour

        thread = threading.Thread(target=cleanup, daemon=True)
        thread.start()

    def cleanup_expired(self) -> None:
        """Remove expired cache entries"""
        with self.lock:
            expired = [url for url, entry in self.cache.items() if entry.is_expired]
            for url in expired:
                entry = self.cache.pop(url)
                try:
                    if os.path.exists(entry.path):
                        os.remove(entry.path)
                except Exception as e:
                    ColorOutput.print_warning(f"Error removing expired cache file: {e}")

            if expired:
                self._save_cache()

    def get(self, url: str) -> Optional[str]:
        """Get cached file path if available and not expired"""
        with self.lock:
            entry = self.cache.get(url)
            if entry and not entry.is_expired and os.path.exists(entry.path):
                return entry.path
            return None

    def put(self, url: str, file_path: str, ttl: Optional[int] = None) -> None:
        """Add file to cache with optional TTL"""
        with self.lock:
            self.cache[url] = CacheEntry(
                path=file_path,
                timestamp=time.time(),
                ttl=ttl or self.default_ttl
            )
            self._save_cache()

# Initialize global cache manager
cache_manager = CacheManager()

class DownloadManager:
    """Enhanced download manager with retry logic, verification and fallback URLs"""
    def __init__(self, max_retries: int = 3, timeout: int = 30,
                 chunk_size: int = 16384, verify_ssl: bool = True):
        self.max_retries = max_retries
        self.timeout = timeout
        self.chunk_size = chunk_size
        self.verify_ssl = verify_ssl
        self._session = self._create_session()

    def _create_session(self):
        """Create URL opener with custom settings"""
        opener = urllib.request.build_opener()
        opener.addheaders = [
            ('User-Agent', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'),
            ('Accept', '*/*')
        ]
        return opener

    def download_file(self, url: str, dest_path: str,
                     fallback_urls: Optional[List[str]] = None,
                     expected_size: Optional[int] = None,
                     hash_value: Optional[str] = None) -> bool:
        """
        Download file with progress bar, retry logic, verification and fallback URLs

        Args:
            url: Primary download URL
            dest_path: Destination path
            fallback_urls: List of alternative URLs to try if primary fails
            expected_size: Expected file size in bytes
            hash_value: Expected SHA256 hash

        Returns:
            bool: Success status
        """
        urls_to_try = [url]
        if fallback_urls:
            urls_to_try.extend(fallback_urls)

        for current_url in urls_to_try:
            ColorOutput.print_debug(f"Trying URL: {current_url}")

            # Check cache first
            cached_path = cache_manager.get(current_url)
            if cached_path:
                try:
                    shutil.copy2(cached_path, dest_path)
                    if self._verify_file(dest_path, expected_size, hash_value):
                        return True
                except Exception as e:
                    ColorOutput.print_warning(f"Cache copy failed: {e}")

            # Download with retries
            for attempt in range(self.max_retries):
                try:
                    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
                        response = self._session.open(current_url, timeout=self.timeout)
                        total_size = int(response.headers.get('content-length', 0))

                        with tqdm(total=total_size, unit='B', unit_scale=True,
                                 desc=f"Downloading {os.path.basename(current_url)}") as pbar:
                            while True:
                                chunk = response.read(self.chunk_size)
                                if not chunk:
                                    break
                                temp_file.write(chunk)
                                pbar.update(len(chunk))

                    # Verify and move to destination
                    if self._verify_file(temp_file.name, expected_size, hash_value):
                        shutil.move(temp_file.name, dest_path)
                        cache_manager.put(current_url, dest_path)
                        return True

                    os.unlink(temp_file.name)

                except Exception as e:
                    ColorOutput.print_warning(f"Download attempt {attempt + 1} failed for {current_url}: {e}")
                    if attempt < self.max_retries - 1:
                        wait_time = 2 ** attempt
                        time.sleep(wait_time)
                    continue

            ColorOutput.print_warning(f"All attempts failed for {current_url}, trying next URL if available")

        ColorOutput.print_error("All download attempts failed")
        return False

    def _verify_file(self, file_path: str, expected_size: Optional[int] = None,
                    hash_value: Optional[str] = None) -> bool:
        """Verify downloaded file integrity"""
        if not os.path.exists(file_path):
            return False

        try:
            file_size = os.path.getsize(file_path)

            # Size check
            if expected_size and file_size != expected_size:
                ColorOutput.print_warning(f"Size mismatch: expected {expected_size}, got {file_size}")
                return False

            # Basic file validation
            if file_size < 100:  # Arbitrary minimum size
                ColorOutput.print_warning("File too small, likely an error page")
                return False

            # Check if file is a valid archive
            if file_path.lower().endswith(('.zip', '.7z')):
                try:
                    with zipfile.ZipFile(file_path, 'r') as zf:
                        # Try to read the archive
                        zf.testzip()
                except Exception as e:
                    ColorOutput.print_warning(f"Invalid archive file: {e}")
                    return False

            # Hash check
            if hash_value:
                file_hash = hashlib.sha256()
                with open(file_path, 'rb') as f:
                    for chunk in iter(lambda: f.read(8192), b''):
                        file_hash.update(chunk)
                if file_hash.hexdigest() != hash_value:
                    ColorOutput.print_warning("Hash mismatch")
                    return False

            return True

        except Exception as e:
            ColorOutput.print_error(f"Error verifying file: {e}")
            return False


class ArchiveHealer:
    """Self-healing archive extraction class with enhanced corruption handling"""
    def __init__(self, archive_path: str):
        self.archive_path = archive_path
        self.incomplete_files: List[str] = []
        self.crc_errors: List[str] = []
        self.repair_attempts: Dict[str, int] = {}
        self.max_repair_attempts = 3
        self.failure_report = FailureReport()

    def verify_archive_integrity(self) -> bool:
        """Verify overall archive integrity with repair attempts"""
        try:
            # First try normal ZIP check
            with zipfile.ZipFile(self.archive_path) as zf:
                bad_file = zf.testzip()
                if not bad_file:
                    return True

                self.crc_errors.append(bad_file)
                ColorOutput.print_warning(f"CRC error detected in {bad_file}")

                # Attempt repair for CRC errors
                if self._repair_crc_errors():
                    return True

            # If normal ZIP check fails, try manual repair
            if self._repair_zip_header():
                return True

            return False

        except zipfile.BadZipFile:
            ColorOutput.print_warning("Bad ZIP file detected, attempting repair...")
            return self._repair_zip_header()
        except Exception as e:
            ColorOutput.print_error(f"Archive integrity check failed: {e}")
            self.failure_report.add_error(self.archive_path, f"Integrity check failed: {e}") #Added error reporting
            return False

    def _repair_zip_header(self) -> bool:
        """Attempt to repair corrupted ZIP headers with enhanced logging"""
        try:
            with open(self.archive_path, 'rb') as f:
                # Log first 16 bytes of the file
                header = f.read(16)
                ColorOutput.print_debug(f"Original file header bytes: {header.hex()}")
                if not header.startswith(b'PK'):
                    ColorOutput.print_debug("File does not start with PK signature")
                    self.failure_report.add_error(self.archive_path, 
                                                  f"Invalid ZIP header: {header[:4].hex()}")
                    return False

                # Read rest of the file
                f.seek(0)
                data = f.read()

            # Look for ZIP end of central directory signature
            eocd_position = data.rfind(b'PK\x05\x06')
            if eocd_position == -1:
                ColorOutput.print_debug("No EOCD signature found")
                self.failure_report.add_error(self.archive_path, 
                                              "Missing end of central directory")
                return False

            # Create temporary file with repaired header
            temp_path = f"{self.archive_path}.tmp"
            with open(temp_path, 'wb') as f:
                # Write ZIP header
                f.write(b'PK\x03\x04')
                # Write rest of file from central directory
                f.write(data[eocd_position:])
                ColorOutput.print_debug(f"Created temporary repaired file: {temp_path}")

            # Verify repaired file
            try:
                with zipfile.ZipFile(temp_path) as zf:
                    if not zf.testzip():
                        # Replace original with repaired version
                        shutil.move(temp_path, self.archive_path)
                        ColorOutput.print_success("Successfully repaired ZIP header")
                        return True
                    else:
                        ColorOutput.print_debug("Repaired file still has CRC errors")
                        self.failure_report.add_warning(self.archive_path, "Repair resulted in CRC errors") #Added warning
            except Exception as e:
                ColorOutput.print_debug(f"Failed to verify repaired file: {e}")
                self.failure_report.add_error(self.archive_path, f"Repair verification failed: {e}") #Added error reporting
            finally:
                if os.path.exists(temp_path):
                    try:
                        os.remove(temp_path)
                        ColorOutput.print_debug("Cleaned up temporary file")
                    except OSError as e:
                        ColorOutput.print_warning(f"Failed to clean up temporary file: {e}")

            return False

        except Exception as e:
            ColorOutput.print_error(f"Header repair failed: {e}")
            self.failure_report.add_error(self.archive_path, f"Repair failed: {e}")
            return False

    def _repair_crc_errors(self) -> bool:
        """Attempt to repair files with CRC errors"""
        success = True
        for file_path in self.crc_errors:
            if not self._repair_single_file(file_path):
                success = False
        return success

    def _repair_single_file(self, file_path: str) -> bool:
        """Attempt to repair a single corrupted file with advanced parallel recovery"""
        if self.repair_attempts.get(file_path, 0) >= self.max_repair_attempts:
            ColorOutput.print_debug(f"Max repair attempts ({self.max_repair_attempts}) reached for {file_path}")
            return False

        try:
            with zipfile.ZipFile(self.archive_path) as zf:
                info = zf.getinfo(file_path)
                is_large_file = info.file_size > 1024 * 1024 * 5  # 5MB threshold
                is_resource_file = any(fnmatch.fnmatch(file_path.lower(), p) 
                                        for patterns in APP_RESOURCE_PATTERNS.values() 
                                        for p in patterns)

                # Diagnostic info
                ColorOutput.print_debug(
                    f"Repair attempt for {file_path}:\n"
                    f"Size: {info.file_size:,} bytes\n"
                    f"Is large file: {is_large_file}\n"
                    f"Is resource file: {is_resource_file}\n"
                    f"CRC: {hex(info.CRC)}"
                )

                # First try direct extraction for small/resource files
                if not is_large_file or is_resource_file:
                    try:
                        with tempfile.NamedTemporaryFile(delete=False) as temp:
                            with zf.open(file_path) as source:
                                shutil.copyfileobj(source, temp)

                            if self._verify_extracted_file(temp.name, file_path):
                                shutil.copy2(temp.name, os.path.join(os.path.dirname(self.archive_path), file_path))
                                return True
                    except Exception as e:
                        ColorOutput.print_debug(f"Direct extraction failed: {e}")
                        self.failure_report.add_error(file_path, f"Direct extraction failed: {e}") #Added error reporting

                # For large files, try parallel extraction
                if is_large_file and info.file_size > 1024 * 1024 * 50:  # 50MB threshold
                    try:
                        with ThreadPoolExecutor(max_workers=4) as executor:
                            chunk_starts = list(range(0, info.file_size, 1024 * 1024))  # 1MB chunks
                            temp_files = []

                            # Extract chunks in parallel
                            futures = []
                            for start in chunk_starts:
                                end = min(start + 1024 * 1024, info.file_size)
                                temp = tempfile.NamedTemporaryFile(delete=False)
                                temp_files.append(temp.name)
                                futures.append(executor.submit(
                                    self._extract_chunk, file_path, start, end, temp.name
                                ))

                            # Wait for all chunks
                            for future in futures:
                                if future.exception():
                                    ColorOutput.print_debug(f"Chunk extraction failed: {future.exception()}")
                                    self.failure_report.add_error(file_path, f"Chunk extraction failed: {future.exception()}") #Added error reporting
                                    return False

                            # Combine chunks
                            with tempfile.NamedTemporaryFile(delete=False) as final:
                                for temp_file in temp_files:
                                    with open(temp_file, 'rb') as f:
                                        shutil.copyfileobj(f, final)
                                final.flush()

                                # Verify and save
                                if self._verify_extracted_file(final.name, file_path):
                                    shutil.copy2(final.name, os.path.join(os.path.dirname(self.archive_path), file_path))
                                    return True

                    except Exception as e:
                        ColorOutput.print_debug(f"Parallel extraction failed: {e}")
                        self.failure_report.add_error(file_path, f"Parallel extraction failed: {e}") #Added error reporting
                    finally:
                        # Cleanup temp files
                        for temp_file in temp_files:
                            try:
                                if os.path.exists(temp_file):
                                    os.remove(temp_file)
                            except OSError as e:
                                ColorOutput.print_warning(f"Failed to clean up temp file: {e}")

                # Sequential extraction if parallel failed or for smaller files
                for chunk_size in [32768, 65536, 131072]:  # Try different chunk sizes
                    try:
                        with zf.open(file_path) as source, tempfile.NamedTemporaryFile(delete=False) as temp:
                            shutil.copyfileobj(source, temp, chunk_size)

                            if self._verify_extracted_file(temp.name, file_path):
                                shutil.copy2(temp.name, os.path.join(os.path.dirname(self.archive_path), file_path))
                                return True

                    except Exception as e:
                        ColorOutput.print_debug(f"Sequential extraction failed with chunk size {chunk_size}: {e}")
                        continue
                    finally:
                        try:
                            if os.path.exists(temp.name):
                                os.remove(temp.name)
                        except OSError as e:
                            ColorOutput.print_warning(f"Failed to clean up temp file: {e}")

                self.repair_attempts[file_path] = self.repair_attempts.get(file_path, 0) + 1
                return False

        except Exception as e:
            ColorOutput.print_error(f"Repair failed for {file_path}: {e}")
            self.failure_report.add_error(file_path, f"Repair failed: {e}") #Added error reporting
            return False

    def _extract_chunk(self, file_path: str, start: int, end: int, output_path: str) -> bool:
        """Extract a specific chunk of a file from the archive"""
        try:
            with zipfile.ZipFile(self.archive_path) as zf, open(output_path, 'wb') as out:
                with zf.open(file_path) as source:
                    source.seek(start)
                    remaining = end - start
                    while remaining > 0:
                        chunk_size = min(remaining, 65536)  # 64KB chunks
                        chunk = source.read(chunk_size)
                        if not chunk:
                            break
                        out.write(chunk)
                        remaining -= len(chunk)
            return True
        except Exception as e:
            ColorOutput.print_debug(f"Chunk extraction failed: {e}")
            self.failure_report.add_error(file_path, f"Chunk extraction failed: {e}") #Added error reporting
            return False

    def _verify_extracted_file(self, temp_path: str, original_path: str) -> bool:
        """Verify an extracted file's integrity"""
        try:
            with zipfile.ZipFile(self.archive_path) as zf:
                info = zf.getinfo(original_path)
                file_size = os.path.getsize(temp_path)

                if file_size != info.file_size:
                    ColorOutput.print_debug(f"Size mismatch: expected {info.file_size}, got {file_size}")
                    return False

                # Calculate CRC32 of extracted file
                crc = 0
                with open(temp_path, 'rb') as f:
                    while True:
                        chunk = f.read(65536)
                        if not chunk:
                            break
                        crc = zlib.crc32(chunk, crc)

                if crc & 0xFFFFFFFF != info.CRC:
                    ColorOutput.print_debug(f"CRC mismatch: expected {hex(info.CRC)}, got {hex(crc & 0xFFFFFFFF)}")
                    return False

                return True

        except Exception as e:
            ColorOutput.print_error(f"Verification failed: {e}")
            self.failure_report.add_error(original_path, f"Verification failed: {e}") #Added error reporting
            return False

# Update APP_RESOURCE_PATTERNS to remove AppImage
APP_RESOURCE_PATTERNS = {
    'win32': ['*.dll', '*.exe', '*.ico', '*.manifest', '*.pdb', 'electron.exe', '*.asar'],
    'darwin': ['*.dylib', '*.app', 'Electron.app', '*.asar'],
    'linux': ['*.so', 'electron', '*.asar']  # Removed AppImage
}

class ElectronAppExtractor:
    """Handle extraction and validation of Electron applications"""
    def __init__(self, base_path: str):
        self.base_path = os.path.abspath(base_path)
        self.failure_report = FailureReport()
        self.resource_dirs = {
            'win32': ['resources', 'locales', 'swiftshader'],
            'darwin': ['Contents/Resources', 'Contents/Frameworks'],
            'linux': ['resources', 'locales', 'lib']
        }

    def identify_electron_app(self) -> bool:
        """Check if the directory contains an Electron application"""
        try:
            package_json = os.path.join(self.base_path, 'package.json')
            if not os.path.exists(package_json):
                return False

            with open(package_json, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # Check for Electron dependencies
            dependencies = {**data.get('dependencies', {}), **data.get('devDependencies', {})}
            return 'electron' in dependencies or 'electron-builder' in dependencies

        except json.JSONDecodeError as e:
            ColorOutput.print_error(f"Invalid package.json format: {e}")
            self.failure_report.add_error('package.json', f"Failed to parse package.json: {e}")
            return False
        except OSError as e:
            ColorOutput.print_error(f"Error reading package.json: {e}")
            self.failure_report.add_error('package.json', f"Failed to read package.json: {e}")
            return False
        except Exception as e:
            ColorOutput.print_error(f"Error identifying Electron app: {e}")
            self.failure_report.add_error('package.json', f"Failed to identify Electron app: {e}")
            return False

    def validate_electron_resources(self) -> bool:
        """Validate Electron application resource files"""
        try:
            # Check required files
            required_files = ['main.js', 'package.json']
            for file in required_files:
                file_path = os.path.join(self.base_path, file)
                if not os.path.exists(file_path):
                    self.failure_report.add_error(file, f"Missing required Electron file: {file}")
                    return False
                if not os.access(file_path, os.R_OK):
                    self.failure_report.add_error(file, f"No read permission for file: {file}")
                    return False

            # Check resource directories
            platform_resources = self.resource_dirs.get(platform.system().lower(), [])
            for resource_dir in platform_resources:
                dir_path = os.path.join(self.base_path, resource_dir)
                if os.path.exists(dir_path):
                    if not os.access(dir_path, os.R_OK):
                        self.failure_report.add_error(dir_path, f"No read permission for directory: {resource_dir}")
                        return False

            # Check for asar archives
            try:
                asar_files = glob.glob(os.path.join(self.base_path, '**', '*.asar'), recursive=True)
                for asar_file in asar_files:
                    if not self._verify_asar_file(asar_file):
                        return False
            except glob.error as e:
                ColorOutput.print_error(f"Error searching for asar files: {e}")
                self.failure_report.add_error(self.base_path, f"Failedtosearch for asar files: {e}")
                return False

            return True

        except Exception as e:
            ColorOutput.print_error(f"Error validating Electron resources: {e}")
            self.failure_report.add_error(self.base_path, f"Resource validation failed: {e}")
            return False

    def _verify_asar_file(self, asar_path: str) -> bool:
        """Verify integrity of an asar archive"""
        try:
            if not os.path.exists(asar_path):
                self.failure_report.add_error(asar_path, "Asar file does not exist")
                return False

            if not os.access(asar_path, os.R_OK):
                self.failure_report.add_error(asar_path, "No read permission for asar file")
                return False

            with open(asar_path, 'rb') as f:
                header = f.read(4)
                if header != b'\x04\x00\x00\x00':  # asar magic number
                    self.failure_report.add_error(asar_path, "Invalid asar archive header")
                    return False

                # Read size field
                size_bytes = f.read(4)
                if len(size_bytes) != 4:
                    self.failure_report.add_error(asar_path, "Truncated asar header")
                    return False

                # Verify file size matches header
                size = int.from_bytes(size_bytes, byteorder='little')
                actual_size = os.path.getsize(asar_path)
                if actual_size < size + 8:  # header size (8) + content size
                    self.failure_report.add_error(asar_path, "Asar file size mismatch")
                    return False

            return True

        except OSError as e:
            ColorOutput.print_error(f"IO error verifying asar file {asar_path}: {e}")
            self.failure_report.add_error(asar_path, f"IO error during asar verification: {e}")
            return False
        except Exception as e:
            ColorOutput.print_error(f"Error verifying asar file {asar_path}: {e}")
            self.failure_report.add_error(asar_path, f"Asar verification failed: {e}")
            return False

    def extract_packaged_electron(self, source_path: str, target_dir: str) -> bool:
        """Extract a packaged Electron application"""
        try:
            source_path = os.path.abspath(source_path)
            target_dir = os.path.abspath(target_dir)

            if not os.path.exists(source_path):
                self.failure_report.add_error(source_path, "Source file does not exist")
                return False

            if not os.path.exists(target_dir):
                try:
                    os.makedirs(target_dir)
                except OSError as e:
                    self.failure_report.add_error(target_dir, f"Failed to create target directory: {e}")
                    return False

            # Handle different package formats (removed AppImage support)
            if source_path.endswith('.asar'):
                return self._extract_asar(source_path, target_dir)
            elif source_path.endswith('.app'):
                return self._extract_app_bundle(source_path, target_dir)
            elif source_path.endswith('.exe'):
                return self._extract_windows_exe(source_path, target_dir)
            else:
                self.failure_report.add_error(source_path, "Unsupported package format")
                return False

        except Exception as e:
            ColorOutput.print_error(f"Error extracting Electron package: {e}")
            self.failure_report.add_error(source_path, f"Extraction failed: {e}")
            return False

    def _extract_asar(self, source_path: str, target_dir: str) -> bool:
        """Extract contents of an asar archive"""
        try:
            if not self._verify_asar_file(source_path):
                return False

            # Ensure target directory exists
            os.makedirs(target_dir, exist_ok=True)

            # For now, just copy the asar file to target
            # TODO: Implement actual asar extraction when needed
            target_path = os.path.join(target_dir, os.path.basename(source_path))
            shutil.copy2(source_path, target_path)
            return True

        except OSError as e:
            ColorOutput.print_error(f"IO error extracting asar archive: {e}")
            self.failure_report.add_error(source_path, f"IO error during asar extraction: {e}")
            return False
        except Exception as e:
            ColorOutput.print_error(f"Error extracting asar archive: {e}")
            self.failure_report.add_error(source_path, f"Asar extraction failed: {e}")
            return False

    def _extract_app_bundle(self, source_path: str, target_dir: str) -> bool:
        """Extract contents of a macOS .app bundle"""
        try:
            if not os.path.isdir(source_path):
                self.failure_report.add_error(source_path, "Not a valid .app bundle")
                return False

            # Verify bundle structure
            required_paths = [
                os.path.join(source_path, 'Contents', 'MacOS'),
                os.path.join(source_path, 'Contents', 'Info.plist')
            ]

            for path in required_paths:
                if not os.path.exists(path):
                    self.failure_report.add_error(source_path, f"Missing required path: {path}")
                    return False
                if not os.access(path, os.R_OK):
                    self.failure_report.add_error(path, f"No read permission for: {path}")
                    return False

            # Copy the entire bundle
            target_bundle = os.path.join(target_dir, os.path.basename(source_path))
            shutil.copytree(source_path, target_bundle, symlinks=True)
            return True

        except OSError as e:
            ColorOutput.print_error(f"IO error extracting app bundle: {e}")
            self.failure_report.add_error(source_path, f"IO error during app bundle extraction: {e}")
            return False
        except Exception as e:
            ColorOutput.print_error(f"Error extracting app bundle: {e}")
            self.failure_report.add_error(source_path, f"App bundle extraction failed: {e}")
            return False

    def _extract_windows_exe(self, source_path: str, target_dir: str) -> bool:
        """Extract contents of a Windows executable"""
        try:
            # Verify PE format
            with open(source_path, 'rb') as f:
                header = f.read(2)
                if header != b'MZ':
                    self.failure_report.add_error(source_path, "Invalid Windows executable format")
                    return False

                # Read PE header offset
                f.seek(0x3C)
                pe_offset = int.from_bytes(f.read(4), byteorder='little')
                f.seek(pe_offset)
                if f.read(4) != b'PE\x00\x00':
                    self.failure_report.add_error(source_path, "Invalid PE header")
                    return False

            # Create target directory
            os.makedirs(target_dir, exist_ok=True)

            # Copy executable and required DLLs
            target_exe = os.path.join(target_dir, os.path.basename(source_path))
            shutil.copy2(source_path, target_exe)

            # Copy associated resource files if they exist
            source_dir = os.path.dirname(source_path)
            for pattern in APP_RESOURCE_PATTERNS['win32']:
                try:
                    for resource in glob.glob(os.path.join(source_dir, pattern)):
                        if os.path.isfile(resource):
                            shutil.copy2(resource, target_dir)
                except (OSError, shutil.Error) as e:
                    ColorOutput.print_warning(f"Error copying resource {resource}: {e}")
                    continue

            return True

        except OSError as e:
            ColorOutput.print_error(f"IO error extracting Windows executable: {e}")
            self.failure_report.add_error(source_path, f"IO error during Windows executable extraction: {e}")
            return False
        except Exception as e:
            ColorOutput.print_error(f"Error extracting Windows executable: {e}")
            self.failure_report.add_error(source_path, f"Windows executable extraction failed: {e}")
            return False

# Add test cases for ElectronAppExtractor
class TestElectronAppExtractor(unittest.TestCase):
    """Test suite for Electron application extraction"""

    def setUp(self):
        self.test_dir = tempfile.mkdtemp()
        self.extractor = ElectronAppExtractor(self.test_dir)

    def tearDown(self):
        try:
            shutil.rmtree(self.test_dir)
        except OSError as e:
            ColorOutput.print_warning(f"Failed to clean up test directory: {e}")

    def test_electron_app_identification(self):
        """Test Electron app identification"""
        # Create mock package.json
        package_json = {
            "name": "test-app",
            "dependencies": {
                "electron": "^13.0.0"
            }
        }
        with open(os.path.join(self.test_dir, 'package.json'), 'w', encoding='utf-8') as f:
            json.dump(package_json, f)

        self.assertTrue(self.extractor.identify_electron_app())

    def test_electron_resource_validation(self):
        """Test Electron resource validation"""
        # Create required files and directories
        os.makedirs(os.path.join(self.test_dir, 'resources'))
        os.makedirs(os.path.join(self.test_dir, 'locales'))

        open(os.path.join(self.test_dir, 'main.js'), 'w').close()
        with open(os.path.join(self.test_dir, 'package.json'), 'w', encoding='utf-8') as f:
            json.dump({"name": "test"}, f)

        self.assertTrue(self.extractor.validate_electron_resources())

    def test_asar_validation(self):
        """Test asar archive validation"""
        asar_path = os.path.join(self.test_dir, 'app.asar')

        # Create mock asar file with valid header and size field
        with open(asar_path, 'wb') as f:
            f.write(b'\x04\x00\x00\x00')  # Magic number
            content_size = 1024
            f.write(content_size.to_bytes(4, byteorder='little'))  # Size field
            f.write(b'\x00' * content_size)  # Dummy content

        self.assertTrue(self.extractor._verify_asar_file(asar_path))

        # Test invalid header
        with open(asar_path, 'wb') as f:
            f.write(b'\x00\x00\x00\x00')  # Invalid magic number

        self.assertFalse(self.extractor._verify_asar_file(asar_path))
        self.assertTrue(any('Invalid asar archive header' in err['message'] 
                          for err in self.extractor.failure_report.errors))

    def test_invalid_formats(self):
        """Test handling of invalid formats"""
        # Test Windows executable format validation
        invalid_exe = os.path.join(self.test_dir, 'invalid.exe')
        with open(invalid_exe, 'wb') as f:
            f.write(b'invalid')

        self.assertFalse(self.extractor._extract_windows_exe(invalid_exe, self.test_dir))
        self.assertTrue(any('Invalid Windows executable format' in err['message'] 
                          for err in self.extractor.failure_report.errors))

        # Test valid PE format
        valid_exe = os.path.join(self.test_dir, 'valid.exe')
        with open(valid_exe, 'wb') as f:
            f.write(b'MZ')  # DOS header
            f.write(b'\x00' * 58)  # Padding
            f.write((0x40).to_bytes(4, byteorder='little'))  # PE header offset
            f.write(b'\x00' * 4)  # More padding
            f.write(b'PE\x00\x00')  # PE signature

        self.assertTrue(self.extractor._extract_windows_exe(valid_exe, self.test_dir))

    def test_io_errors(self):
        """Test handling of IO errors during extraction"""
        # Test read permission error
        no_access_dir = os.path.join(self.test_dir, 'no_access')
        os.makedirs(no_access_dir)
        test_file = os.path.join(no_access_dir, 'test.exe')

        with open(test_file, 'wb') as f:
            f.write(b'MZ')  # Valid DOS header

        try:
            os.chmod(no_access_dir, 0o000)  # Remove all permissions
            self.assertFalse(self.extractor._extract_windows_exe(test_file, self.test_dir))
            self.assertTrue(any('permission' in err['message'].lower() 
                              for err in self.extractor.failure_report.errors))
        finally:
            os.chmod(no_access_dir, 0o755)  # Restore permissions for cleanup

class TestExecutableExtractor(unittest.TestCase):
    """Test suite for executable extractor"""

    def setUp(self):
        self.test_dir = tempfile.mkdtemp()
        self.cache_manager = CacheManager(cache_dir=os.path.join(self.test_dir, 'cache'))
        self.download_manager = DownloadManager()

    def tearDown(self):
        shutil.rmtree(self.test_dir)

    def test_cache_management(self):
        """Test cache operations"""
        test_url = "https://example.com/test.zip"
        test_file = os.path.join(self.test_dir, "test.txt")

        # Create test file
        with open(test_file, 'w') as f:
            f.write("test content")

        # Test cache put
        self.cache_manager.put(test_url, test_file)

        # Test cache get
        cached_path = self.cache_manager.get(test_url)
        self.assertIsNotNone(cached_path)

        # Test cache expiration
        time.sleep(2)
        entry = self.cache_manager.cache[test_url]
        entry.ttl = 1  # Set TTL to 1 second
        cached_path = self.cache_manager.get(test_url)
        self.assertIsNone(cached_path)

    def test_file_system_checks(self):
        """Test file system operations"""
        test_file = os.path.join(self.test_dir, "test.txt")

        # Test permission checks
        self.assertTrue(FileSystemChecker.check_permissions(self.test_dir))

        # Test disk space check
        self.assertTrue(FileSystemChecker.check_disk_space(self.test_dir, 1024))

        # Test invalid path
        invalid_path = "/invalid/path/test.txt"
        self.assertFalse(FileSystemChecker.check_permissions(invalid_path))

    def test_archive_healing(self):
        """Test archive repair functionality with simulated corruption"""
        # Create test archive
        test_archive = os.path.join(self.test_dir, "test.zip")
        with zipfile.ZipFile(test_archive, 'w') as zf:
            zf.writestr("test.txt", "test content" * 100)  # Make file bigger for better corruption test

        healer = ArchiveHealer(test_archive)

        # Test basic integrity
        self.assertTrue(healer.verify_archive_integrity())

        # Simulate corruption by writing bad data
        try:
            with open(test_archive, 'r+b') as f:
                f.seek(20)  # Seek to a position after header
                f.write(b'CORRUPT')  # Write some corrupting bytes
                f.flush()  # Ensure data is written
                os.fsync(f.fileno())  # Force write to disk
        except Exception as e:
            self.fail(f"Failed to simulate corruption: {e}")

        # Test corruption detection
        healer = ArchiveHealer(test_archive)  # Create new instance to avoid caching
        self.assertFalse(healer.verify_archive_integrity())
        self.assertGreater(len(healer.failure_report.errors), 0)

        # Test repair attempt
        repaired = healer._repair_single_file("test.txt")
        self.assertTrue(repaired)


    def test_io_error_handling(self):
        """Test handling of various IO errors"""
        # Test non-existent file
        non_existent = os.path.join(self.test_dir, "nonexistent.zip")
        healer = ArchiveHealer(non_existent)
        self.assertFalse(healer.verify_archive_integrity())
        self.assertIn("not exist", healer.failure_report.errors[0]['message'].lower())

        # Test permission error
        test_file = os.path.join(self.test_dir, "readonly.zip")
        try:
            with open(test_file, 'w') as f:
                f.write("test")

            # Make read-only
            os.chmod(test_file, 0o444)
            self.assertFalse(FileSystemChecker.check_permissions(test_file))

            # Try to modify read-only file
            with self.assertRaises(PermissionError):
                with open(test_file, 'w') as f:
                    f.write("test")

        finally:
            # Cleanup: restore permissions to allow deletion
            os.chmod(test_file, 0o644)

        # Test disk space error
        huge_size = 1024 * 1024 * 1024 * 1024  # 1TB
        self.assertFalse(FileSystemChecker.check_disk_space(self.test_dir, huge_size))

        # Test invalid path characters
        invalid_path = os.path.join(self.test_dir, "test\0with\0null.zip")
        with self.assertRaises(Exception):
            with open(invalid_path, 'w') as f:
                f.write("test")

    def test_failure_reporting(self):
        """Test the FailureReport functionality"""
        report = FailureReport()

        # Test error reporting
        report.add_error("test.txt", "Test error")
        self.assertEqual(len(report.errors), 1)
        self.assertEqual(report.errors[0]['file'], "test.txt")

        # Test warning reporting
        report.add_warning("test.txt", "Test warning")
        self.assertEqual(len(report.warnings), 1)

        # Test report generation
        full_report = report.get_report()
        self.assertEqual(full_report['total_errors'], 1)
        self.assertEqual(full_report['total_warnings'], 1)

    def test_concurrent_operations(self):
        """Test concurrent processing with error handling"""
        results = []
        errors = []
        processed = threading.Event()

        def process_with_error(x):
            try:
                if x == 2:
                    raise ValueError("Simulated error")
                result = x * x
                time.sleep(0.1)  # Simulate work
                return result
            except Exception as e:
                errors.append(str(e))
                raise
            finally:
                if not processed.is_set():
                    processed.set()

        with ThreadPoolExecutor(max_workers=4) as executor:
            futures = []
            for i in range(4):
                future = executor.submit(process_with_error, i)
                futures.append(future)

            # Wait for all futures with timeout
            try:
                done, not_done = concurrent.futures.wait(
                    futures, 
                    timeout=5,
                    return_when=concurrent.futures.ALL_COMPLETED
                )

                # Cancel any remaining futures
                for future in not_done:
                    future.cancel()

                # Collect results
                for future in done:
                    try:
                        if not future.cancelled():
                            result = future.result(timeout=1)
                            if result is not None:
                                results.append(result)
                    except ValueError as e:
                        # Expected error for x == 2
                        self.assertIn("Simulated error", str(e))
                    except Exception as e:
                        self.fail(f"Unexpected error: {e}")

            except concurrent.futures.TimeoutError:
                self.fail("Test timed out")

        # Verify results
        self.assertEqual(sorted(results), [0, 1, 9])  # 0, 1, and 9 (3^2)
        self.assertEqual(len(errors), 1)
        self.assertIn("Simulated error", errors[0])

    def test_memory_monitoring(self):
        """Test memory monitoring"""
        initial_memory = MemoryMonitor.get_memory_usage()
        self.assertIsInstance(initial_memory, float)

        # Test memory limit check
        self.assertTrue(MemoryMonitor.check_memory_limit(limit_mb=psutil.virtual_memory().total/1024/1024))

    def test_large_file_handling(self):
        """Test handling of large files"""
        large_file_size = 10 * 1024 * 1024  # 10MB
        test_file = os.path.join(self.test_dir, "large.txt")

        # Create large test file
        with open(test_file, 'wb') as f:
            f.write(b'0' * large_file_size)

        # Test memory efficient processing
        chunk_size = 1024 * 1024  # 1MB chunks
        total_read = 0

        with open(test_file, 'rb') as f:
            while True:
                chunk = f.read(chunk_size)
                if not chunk:
                    break
                total_read += len(chunk)

        self.assertEqual(total_read, large_file_size)

    def test_error_handling(self):
        """Test error handling scenarios"""
        # Test invalid file
        with self.assertRaises(Exception):
            with zipfile.ZipFile("/nonexistent/file.zip") as zf:
                pass

        # Test timeout handling
        with self.assertRaises(TimeoutException):
            with time_limit(1):
                time.sleep(2)

def run_tests():
    """Run all tests"""
    suite = unittest.TestLoader().loadTestsFromTestCase(TestExecutableExtractor)
    unittest.TextTestRunner(verbosity=2).run(suite)
    suite = unittest.TestLoader().loadTestsFromTestCase(TestElectronAppExtractor)
    unittest.TextTestRunner(verbosity=2).run(suite)


if __name__ == "__main__":
    try:
        # Configure color output first
        ColorOutput.configure(enable_color=True, log_level=logging.DEBUG)

        # Run tests if in test mode
        if os.environ.get('RUN_TESTS') == '1':
            ColorOutput.print_info("Running tests...")
            run_tests()
        else:
            ColorOutput.print_info("Starting normal execution...")
            # Normal execution code here

    except KeyboardInterrupt:
        ColorOutput.print_warning("Operation interrupted by user")
        sys.exit(1)
    except Exception as e:
        ColorOutput.print_error(f"Fatal error: {e}\n{traceback.format_exc()}")
        sys.exit(1)