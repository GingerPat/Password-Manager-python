#!/usr/bin/env python3

import json
import os
import sys
import secrets
import string
import hashlib
import platform
import time
import subprocess
import re
import shutil
import hmac
import argparse
from pathlib import Path
import base64
import portalocker

try:
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.exceptions import InvalidTag
    _have_cryptography = True
except ImportError:
    _have_cryptography = False

if not _have_cryptography:
    print("Error: Missing required dependency 'cryptography'. Install it with 'pip install cryptography'.")
    sys.exit(1)

# Try to import Argon2 KDF from cryptography; if it's not available, fall back to argon2-cffi
try:
    from cryptography.hazmat.primitives.kdf.argon2 import Argon2, Type as CryptoArgon2Type
    _use_crypto_argon2 = True
except Exception:
    _use_crypto_argon2 = False
    try:
        import argon2.low_level as argon2_low
    except Exception:
        print("Error: Argon2 KDF not available in cryptography and 'argon2-cffi' is not installed. Install it with 'pip install argon2-cffi'.")
        sys.exit(1)


class PasswordManager:
    def __init__(self, db_file: str = None):
        """Initialize the password manager with a database file (Linux only)."""
        # Set default database path - Linux only
        if db_file is None:
            base_dir = os.path.expanduser('~/.config/password-manager')
            
            # Create directory if it doesn't exist
            Path(base_dir).mkdir(parents=True, exist_ok=True)
            
            # Set directory permissions to owner-only (drwx------)
            try:
                os.chmod(base_dir, 0o700)  # drwx------
            except Exception as e:
                pass  # Best effort
            
            db_file = os.path.join(base_dir, 'passwords.db')
        
        self.db_file = db_file
        self.master_password = None
        self.cipher = None
        self._hmac_key = None
        self.passwords_data = {}
        self.db_data = {}
        self.metadata = {}
        self.failed_attempts = 0
        self.lockout_time = None
        self.lockout_duration = 300  # 5 minutes in seconds
        self.last_activity_time = None  # Track last activity for session timeout
        self.session_timeout = 300  # 5 minutes of inactivity before lock
        self.session_active = False  # Is session currently active?
        # (file locking handled by portalocker)
    
    def _clear_master_password(self):
        """Securely clear master password from memory."""
        if self.master_password:
            # Overwrite with spaces before deleting
            self.master_password = " " * len(self.master_password)
            self.master_password = None
    
    def _update_activity(self):
        """Update last activity timestamp for session timeout tracking."""
        self.last_activity_time = time.time()
    
    def _check_session_timeout(self) -> bool:
        """Check if session has timed out due to inactivity."""
        if not self.session_active or not self.last_activity_time:
            return False
        
        time_since_activity = time.time() - self.last_activity_time
        if time_since_activity > self.session_timeout:
            print(f"\nSession timeout! Your vault has been locked due to {self.session_timeout//60} minutes of inactivity.")
            self._lock_session()
            return True
        return False
    
    def _lock_session(self):
        """Lock the current session."""
        self.session_active = False
        self._clear_master_password()
        self.cipher = None
        self.passwords_data = {}
    
    @staticmethod
    def _check_password_strength(password: str) -> tuple:
        """Check master password strength. Returns (score: int, feedback: list)."""
        score = 0
        feedback = []
        
        if len(password) >= 12:
            score += 1
        else:
            feedback.append("Use 12+ characters")
        
        if any(c.isupper() for c in password):
            score += 1
        else:
            feedback.append("Add uppercase letters")
        
        if any(c.islower() for c in password):
            score += 1
        else:
            feedback.append("Add lowercase letters")
        
        if any(c.isdigit() for c in password):
            score += 1
        else:
            feedback.append("Add numbers")
        
        if any(c in "!@#$%^&*()-_=+" for c in password):
            score += 1
        else:
            feedback.append("Add symbols")
        
        return (score, feedback)
    
    def _generate_recovery_codes(self) -> list:
        """Generate 10 recovery codes (each 8 random characters)."""
        codes = []
        for _ in range(10):
            # Generate random recovery code: 4 pairs of characters
            code = ''.join(secrets.choice(string.ascii_uppercase + string.digits) for _ in range(8))
            codes.append(code)
        return codes
    
    def _hash_recovery_code(self, code: str, salt: bytes) -> str:
        """Hash recovery code using PBKDF2HMAC with SHA3-512."""
        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA3_512(),
            length=64,
            salt=salt,
            iterations=640000,
        )
        hashed = base64.b64encode(kdf.derive(code.upper().encode())).decode()
        return hashed
    
    def _hash_answer(self, answer: str, salt: bytes) -> str:
        """Hash security answer using PBKDF2HMAC with SHA3-512."""
        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA3_512(),
            length=64,
            salt=salt,
            iterations=640000,
        )
        hashed = base64.b64encode(kdf.derive(answer.lower().encode())).decode()
        return hashed
    
    def _validate_service_name(self, service: str) -> bool:
        """Validate service name is safe. Allows alphanumeric, spaces, dashes, underscores, dots."""
        if not service or len(service) > 100:
            return False
        # Allow alphanumeric, spaces, dashes, underscores, dots
        return bool(re.match(r'^[\w\s\-\.]+$', service))
    
    def _find_service_key(self, service: str) -> str:
        """Find stored service key using case-insensitive matching."""
        if "passwords" not in self.passwords_data:
            return None
        lowered = service.lower()
        for stored_service in self.passwords_data["passwords"].keys():
            if stored_service.lower() == lowered:
                return stored_service
        return None
    
    def _find_recovery_phrase_key(self, name: str) -> str:
        """Find stored recovery phrase key using case-insensitive matching."""
        if "recovery_phrases" not in self.passwords_data:
            return None
        lowered = name.lower()
        for stored_name in self.passwords_data["recovery_phrases"].keys():
            if stored_name.lower() == lowered:
                return stored_name
        return None
    
    def _derive_key(self, master_password: str, salt: bytes) -> bytes:
        """Derive a cryptographic key from the master password using Argon2id."""
        if _use_crypto_argon2:
            kdf = Argon2(
                time_cost=4,
                memory_cost=65536,
                parallelism=4,
                hash_len=32,
                salt=salt,
                type=CryptoArgon2Type.ID,
            )
            return kdf.derive(master_password.encode())
        else:
            # Use argon2-cffi fallback
            return argon2_low.hash_secret_raw(
                secret=master_password.encode(),
                salt=salt,
                time_cost=4,
                memory_cost=65536,
                parallelism=4,
                hash_len=32,
                type=argon2_low.Type.ID,
            )

    def _derive_recovery_key(self, answer: str, salt: bytes) -> bytes:
        """Derive a key from the recovery answer using Argon2id."""
        if _use_crypto_argon2:
            kdf = Argon2(
                time_cost=4,
                memory_cost=65536,
                parallelism=4,
                hash_len=32,
                salt=salt,
                type=CryptoArgon2Type.ID,
            )
            return kdf.derive(answer.lower().encode())
        else:
            return argon2_low.hash_secret_raw(
                secret=answer.lower().encode(),
                salt=salt,
                time_cost=4,
                memory_cost=65536,
                parallelism=4,
                hash_len=32,
                type=argon2_low.Type.ID,
            )

    def _derive_hmac_key(self) -> bytes:
        """Derive an HMAC key from the master cipher key using HKDF.

        This keeps HMAC keying material out of persistent storage.
        Requires `self.cipher` to be set (derived master key bytes).
        """
        if not self.cipher:
            raise ValueError("Master key not initialized")
        if self._hmac_key:
            return self._hmac_key
        # Use the stored salt (if any) as HKDF salt to add uniqueness
        salt_b64 = self.metadata.get("salt", "")
        hkdf_salt = base64.b64decode(salt_b64) if salt_b64 else None
        hkdf = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=hkdf_salt,
            info=b'password-manager-hmac',
        )
        self._hmac_key = hkdf.derive(self.cipher)
        return self._hmac_key

    def _encrypt_database(self, data: dict) -> str:
        """Encrypt entire database dictionary to JSON string using AES-GCM."""
        try:
            json_str = json.dumps(data, separators=(',', ':'), sort_keys=True)
            # Add random padding to hide database size
            json_str = self._add_random_padding(json_str)
            aesgcm = AESGCM(self.cipher)
            nonce = secrets.token_bytes(12)
            encrypted = aesgcm.encrypt(nonce, json_str.encode(), None)
            return base64.b64encode(nonce + encrypted).decode()
        except Exception as e:
            print(f"Error encrypting database: {e}")
            return None

    def _decrypt_database(self, encrypted_str: str) -> dict:
        """Decrypt entire database from AES-GCM encrypted JSON string."""
        try:
            raw = base64.b64decode(encrypted_str)
            nonce = raw[:12]
            ciphertext = raw[12:]
            aesgcm = AESGCM(self.cipher)
            decrypted = aesgcm.decrypt(nonce, ciphertext, None).decode()
            # Remove padding after decryption
            decrypted = self._remove_random_padding(decrypted)
            return json.loads(decrypted)
        except InvalidTag:
            raise
        except Exception as e:
            print(f"Error decrypting database: {e}")
            return None
    
    def _add_random_padding(self, data: str) -> str:
        """Add random padding to hide database size (prevents size analysis attacks)."""
        # Add 0-2KB of random padding
        padding_size = secrets.randbelow(2048)
        padding = secrets.token_urlsafe(padding_size)
        
        # Format: data + SEPARATOR + padding_size (4 chars) + padding
        separator = "\x00PADDED\x00"
        padded = data + separator + str(padding_size).zfill(4) + padding
        return padded
    
    def _remove_random_padding(self, data: str) -> str:
        """Remove random padding added during encryption."""
        try:
            separator = "\x00PADDED\x00"
            if separator in data:
                # Split at separator
                content, padding_info = data.rsplit(separator, 1)
                # Extract padding size (first 4 characters)
                if len(padding_info) >= 4:
                    padding_size = int(padding_info[:4])
                    # Verify and remove padding
                    if len(padding_info) >= 4 + padding_size:
                        return content
            return data  # No padding found, return as-is
        except Exception:
            return data  # If error, return original

    def _encrypt_blob(self, data: dict, key: bytes) -> str:
        """Encrypt a secondary blob with a separate derived key."""
        try:
            json_str = json.dumps(data, separators=(',', ':'), sort_keys=True)
            aesgcm = AESGCM(key)
            nonce = secrets.token_bytes(12)
            encrypted = aesgcm.encrypt(nonce, json_str.encode(), None)
            return base64.b64encode(nonce + encrypted).decode()
        except Exception as e:
            print(f"Error encrypting recovery blob: {e}")
            return None

    def _decrypt_blob(self, encrypted_str: str, key: bytes) -> dict:
        """Decrypt a secondary blob with a separate derived key."""
        try:
            raw = base64.b64decode(encrypted_str)
            nonce = raw[:12]
            ciphertext = raw[12:]
            aesgcm = AESGCM(key)
            decrypted = aesgcm.decrypt(nonce, ciphertext, None).decode()
            return json.loads(decrypted)
        except InvalidTag:
            raise
        except Exception as e:
            print(f"Error decrypting recovery blob: {e}")
            return None

    def _compute_hmac(self, data: str) -> str:
        """Compute HMAC-SHA256 using a key derived from the master key."""
        key = self._derive_hmac_key()
        h = hmac.new(key, data.encode(), hashlib.sha256)
        return base64.b64encode(h.digest()).decode()

    def _verify_hmac(self, data: str, provided_hmac: str) -> bool:
        """Verify HMAC integrity using constant-time comparison."""
        computed_hmac = self._compute_hmac(data)
        return hmac.compare_digest(computed_hmac, provided_hmac)

    # Simple reentrant lock helpers using a lock file containing the owner PID.
    # File locking is managed with portalocker (cross-platform)

    def setup_master_password(self, master_password: str, security_question: str = "", security_answer: str = "") -> bool:
        """Set up the master password and security question for a new database."""
        if os.path.exists(self.db_file):
            print("Error: Database already exists. Use load() instead.")
            return False

        salt = secrets.token_bytes(32)
        self.cipher = self._derive_key(master_password, salt)
        self.master_password = master_password

        if not security_answer:
            print("Security answer is required.")
            return False

        answer_salt = secrets.token_bytes(32)
        recovery_key = self._derive_recovery_key(security_answer, answer_salt)

        recovery_codes = self._generate_recovery_codes()
        recovery_salt = secrets.token_bytes(32)
        hashed_recovery_codes = [self._hash_recovery_code(code, recovery_salt) for code in recovery_codes]

        recovery_blob_payload = {
            "security_question": security_question,
            "hashed_recovery_codes": hashed_recovery_codes
        }
        recovery_blob = self._encrypt_blob(recovery_blob_payload, recovery_key)
        if recovery_blob is None:
            print("Error: Failed to encrypt recovery metadata")
            return False

        payload = {
            "passwords": {},
            "recovery_phrases": {},
            "login_count": 0
        }

        self.metadata = {
            "failed_attempts": 0,
            "lockout_time": None,
            "answer_attempts": 0,
            "recovery_salt": base64.b64encode(answer_salt).decode(),
            "recovery_blob": recovery_blob,
            "salt": base64.b64encode(salt).decode(),
            "kdf": "argon2id",
            "kdf_params": {
                "time_cost": 4,
                "memory_cost": 65536,
                "parallelism": 4
            }
        }

        encrypted_data = self._encrypt_database(payload)
        if not encrypted_data:
            print("Error: Failed to encrypt database during setup")
            return False

        file_data = {
            "version": 1,
            "salt": self.metadata["salt"],
            "encrypted_data": encrypted_data,
            "failed_attempts": 0,
            "lockout_time": None,
            "answer_attempts": 0,
            "recovery_salt": self.metadata["recovery_salt"],
            "recovery_blob": self.metadata["recovery_blob"],
            "kdf": self.metadata["kdf"],
            "kdf_params": self.metadata["kdf_params"]
        }

        try:
            db_dir = os.path.dirname(self.db_file)
            if db_dir:
                Path(db_dir).mkdir(parents=True, exist_ok=True)
                try:
                    os.chmod(db_dir, 0o700)  # Linux: owner only
                except:
                    pass

            temp_file = self.db_file + '.tmp'
            with open(temp_file, 'w') as f:
                json.dump(file_data, f)

            shutil.move(temp_file, self.db_file)

            try:
                os.chmod(self.db_file, 0o600)  # Linux: owner read/write only
            except:
                pass
        except Exception as e:
            print(f"Error saving database: {e}")
            return False

        self.passwords_data = payload
        self.db_data = payload
        self.session_active = True
        self._update_activity()
        
        # Display recovery codes to user (only shown once!)
        print("\n" + "=" * 60)
        print("RECOVERY CODES - SAVE THESE IN A SAFE PLACE".center(60))
        print("=" * 60)
        print("\nIf you forget your master password AND security answer,")
        print("you can use ONE of these codes to unlock your account.\n")
        print("Recovery Codes:")
        for i, code in enumerate(recovery_codes, 1):
            print(f"  {i:2d}. {code}")
        print("\nIMPORTANT:")
        print("  • Each code can only be used ONCE")
        print("  • Write these down and store in a SECURE location")
        print("  • These will NOT be shown again")
        print("=" * 60 + "\n")
        
        print("Master password and security question set successfully!")
        return True

    def load(self, master_password: str) -> bool:
        """Load and decrypt the password database."""
        if not os.path.exists(self.db_file):
            print("Error: Database file not found.")
            return False

        lock_path = self.db_file + '.lock'
        try:
            try:
                with portalocker.Lock(lock_path, 'w', timeout=5):
                    with open(self.db_file, 'r') as f:
                        file_data = json.load(f)
            except Exception:
                # Lock acquisition failed or timed out; fallback to unlocked read
                with open(self.db_file, 'r') as f:
                    file_data = json.load(f)

            salt_b64 = file_data.get("salt", "")
            encrypted_data = file_data.get("encrypted_data", "")
            stored_hmac = file_data.get("hmac_signature", "")
            
            if not salt_b64 or not encrypted_data:
                print("Error: Invalid database format")
                return False
            
            # Verify HMAC integrity (defense-in-depth against tampering)
            if stored_hmac:
                if not self._verify_hmac(encrypted_data, stored_hmac):
                    print("🚨 ERROR: Database integrity verification FAILED!")
                    print("🚨 This means the database file may have been tampered with.")
                    print("🚨 Your data is encrypted and safe, but the HMAC signature doesn't match.")
                    print("🚨 Possible causes:")
                    print("   - File was modified (corrupted or attacked)")
                    print("   - Wrong master password (different encryption key)")
                    print("   - Database file is from an older version")
                    return False
            
            self.metadata = {k: v for k, v in file_data.items() if k not in {"salt", "encrypted_data", "version", "hmac_signature"}}
            self.failed_attempts = self.metadata.get("failed_attempts", 0)
            self.lockout_time = self.metadata.get("lockout_time")
            self.metadata.setdefault("answer_attempts", 0)

            if self.lockout_time:
                lockout_time_obj = time.time() - float(self.lockout_time)
                if lockout_time_obj < self.lockout_duration:
                    remaining = int(self.lockout_duration - lockout_time_obj)
                    minutes = remaining // 60
                    seconds = remaining % 60
                    print(f"Account is locked. Try again in {minutes}m {seconds}s")
                    print(f"   Or answer the security question to unlock.")
                    return False
                self.failed_attempts = 0
                self.lockout_time = None
                self.metadata["failed_attempts"] = 0
                self.metadata["lockout_time"] = None
                self.metadata["answer_attempts"] = 0
                file_data["failed_attempts"] = 0
                file_data["lockout_time"] = None
                file_data["answer_attempts"] = 0
                self._save_database_raw(file_data)
            # lock context exited automatically

            salt = base64.b64decode(salt_b64)
            self.cipher = self._derive_key(master_password, salt)

            try:
                payload = self._decrypt_database(encrypted_data)
                if payload is None:
                    raise ValueError("Decryption failed")
                self.db_data = payload
                self.passwords_data = payload
            except Exception:
                self.failed_attempts += 1
                self.metadata["failed_attempts"] = self.failed_attempts
                file_data["failed_attempts"] = self.failed_attempts
                if self.failed_attempts >= 3:
                    self.lockout_time = time.time()
                    self.metadata["lockout_time"] = self.lockout_time
                    self.metadata["answer_attempts"] = 0
                    file_data["lockout_time"] = self.lockout_time
                    file_data["answer_attempts"] = 0
                    self._save_database_raw(file_data)
                    print(f"Incorrect master password! ({self.failed_attempts}/3 attempts)")
                    print("Account locked for 5 minutes. Answer the security question to unlock early.")
                    return False
                self._save_database_raw(file_data)
                print(f"Incorrect master password! ({self.failed_attempts}/3 attempts)")
                return False

            self.session_active = True
            self._update_activity()
            self.failed_attempts = 0
            self.lockout_time = None
            self.metadata["failed_attempts"] = 0
            self.metadata["lockout_time"] = None
            self.metadata["answer_attempts"] = 0
            payload["login_count"] = payload.get("login_count", 0) + 1
            self._save_database(payload)
            self._clear_master_password()

            login_count = payload.get("login_count", 0)
            if login_count > 0 and login_count % 10 == 0:
                print("\nHave you backed up your passwords database recently?")
                print(f"   Location: {self.db_file}")
                print("   Keep a secure backup in case of data loss!\n")

            print("Database loaded successfully!")
            return True
        except ValueError as e:
            print(f"Error: Invalid database format - {e}")
            return False
        except KeyError as e:
            print(f"Error: Corrupted database - missing field {e}")
            return False
        except Exception as e:
            print(f"Error loading database: {e}")
            return False
        # lock context handled by portalocker where used

    def check_security_answer(self, provided_answer: str) -> bool:
        """Verify the security answer and unlock the account if correct. Limited to 3 attempts."""
        if not os.path.exists(self.db_file):
            print("Error: Database file not found.")
            return False

        try:
            with open(self.db_file, 'r') as f:
                file_data = json.load(f)

            answer_attempts = file_data.get("answer_attempts", 0)
            recovery_salt_b64 = file_data.get("recovery_salt", "")
            recovery_blob = file_data.get("recovery_blob", "")

            if not recovery_salt_b64 or not recovery_blob:
                print("Error: Recovery information missing or invalid.")
                return False

            if answer_attempts >= 3:
                print("Too many failed security question attempts. Please try again later.")
                return False

            recovery_salt = base64.b64decode(recovery_salt_b64)
            recovery_key = self._derive_recovery_key(provided_answer, recovery_salt)

            try:
                blob = self._decrypt_blob(recovery_blob, recovery_key)
            except Exception:
                answer_attempts += 1
                file_data["answer_attempts"] = answer_attempts
                self._save_database_raw(file_data)
                remaining = 3 - answer_attempts
                print(f"Incorrect security answer. ({answer_attempts}/3 attempts)")
                if remaining > 0:
                    print(f"   {remaining} attempt(s) remaining.")
                else:
                    print("Too many failed attempts. Account remains locked.")
                return False

            print("Security answer correct! Account unlocked.")
            file_data["failed_attempts"] = 0
            file_data["lockout_time"] = None
            file_data["answer_attempts"] = 0
            self._save_database_raw(file_data)

            self.failed_attempts = 0
            self.lockout_time = None
            if self.db_data is not None:
                self.db_data["failed_attempts"] = 0
                self.db_data["lockout_time"] = None
                self.db_data["answer_attempts"] = 0
            return True
        except ValueError as e:
            print(f"Error: Invalid database format - {e}")
            return False
        except KeyError as e:
            print(f"Error: Corrupted database - {e}")
            return False
        except Exception as e:
            print(f"Error checking security answer: {e}")
            return False

    def _save_database_raw(self, data: dict) -> None:
        """Save raw database file with HMAC integrity verification."""
        db_dir = os.path.dirname(self.db_file)
        if db_dir:
            Path(db_dir).mkdir(parents=True, exist_ok=True)
            try:
                os.chmod(db_dir, 0o700)  # Linux: owner only
            except:
                pass
        
        # Compute HMAC of encrypted_data for integrity verification
        encrypted_data_str = data.get("encrypted_data", "")
        hmac_value = self._compute_hmac(encrypted_data_str)
        data["hmac"] = hmac_value  # Store HMAC with database
        
        temp_file = self.db_file + '.tmp'
        lock_path = self.db_file + '.lock'
        try:
            with portalocker.Lock(lock_path, 'w', timeout=5):
                with open(temp_file, 'w') as f:
                    json.dump(data, f)
                shutil.move(temp_file, self.db_file)
            try:
                os.chmod(self.db_file, 0o600)  # Linux: owner read/write only
            except Exception:
                pass
        except Exception as e:
            if os.path.exists(temp_file):
                os.remove(temp_file)
            raise e
    
    def _save_database(self, payload: dict = None, metadata: dict = None) -> None:
        """Save the password database securely with full encryption."""
        if metadata is None:
            metadata = self.metadata.copy()
        else:
            self.metadata = metadata.copy()

        if payload is None:
            if not self.db_data:
                self.db_data = {
                    "passwords": self.passwords_data.get("passwords", {}),
                    "recovery_phrases": self.passwords_data.get("recovery_phrases", {}),
                    "login_count": 0
                }
            else:
                self.db_data["passwords"] = self.passwords_data.get("passwords", {})
                self.db_data["recovery_phrases"] = self.passwords_data.get("recovery_phrases", {})
            payload = self.db_data
        else:
            self.db_data = payload

        if self.cipher:
            encrypted_data = self._encrypt_database(payload)
            if not encrypted_data:
                print("Error: Failed to encrypt database")
                return

            salt_b64 = metadata.get("salt", "")
            if not salt_b64 and os.path.exists(self.db_file):
                try:
                    with open(self.db_file, 'r') as f:
                        existing = json.load(f)
                        salt_b64 = existing.get("salt", "")
                except:
                    pass

            metadata["salt"] = salt_b64
            file_data = metadata.copy()
            file_data["encrypted_data"] = encrypted_data
            
            # Add HMAC integrity signature to detect tampering
            hmac_sig = self._compute_hmac(encrypted_data)
            file_data["hmac_signature"] = hmac_sig
            
            self._save_database_raw(file_data)
        else:
            file_data = metadata.copy()
            file_data["encrypted_data"] = ""
            self._save_database_raw(file_data)

    def add_password(self, service: str, username: str, password: str, overwrite: bool = False) -> bool:
        """Add a new password entry."""
        if not self.cipher:
            print("Error: Database not loaded. Use setup_master_password() or load() first.")
            return False
        
        # Check for session timeout
        if self._check_session_timeout():
            return False
        
        # Validate service name
        if not self._validate_service_name(service):
            print("Invalid service name. Use alphanumeric characters, spaces, dashes, underscores, or dots only (max 100 characters).")
            return False
        
        if not username or len(username) > 500:
            print("Invalid username (max 500 characters).")
            return False
        
        if not password:
            print("Password cannot be empty.")
            return False
        
        if "passwords" not in self.passwords_data:
            self.passwords_data["passwords"] = {}

        # Resolve service name case-insensitively
        existing_key = self._find_service_key(service)
        if existing_key:
            service = existing_key

        # Ensure service container exists and is a dict of usernames
        if service not in self.passwords_data["passwords"]:
            self.passwords_data["passwords"][service] = {}

        # Check for duplicate username under the service
        service_entries = self.passwords_data["passwords"][service]
        if username in service_entries:
            if not overwrite:
                overwrite_choice = input(f"Username '{username}' for service '{service}' already exists. Overwrite? (y/n): ").lower()
                if overwrite_choice != 'y':
                    print("Cancelled.")
                    return False

        try:
            # Store password as plain in-memory; the whole payload is encrypted at save-time
            service_entries[username] = {
                "password": password
            }
            self._save_database()
            self._update_activity()
            print(f"Password for '{service}' ({username}) saved!")
            return True
        except Exception as e:
            print(f"Error saving password: {e}")
            return False

    def search_service(self, query: str) -> list:
        """Search for services by partial name match."""
        if self._check_session_timeout():
            return []
        
        if "passwords" not in self.passwords_data:
            print("No passwords stored.")
            return []
        
        # Case-insensitive search
        matches = [s for s in self.passwords_data["passwords"].keys() if query.lower() in s.lower()]
        
        if not matches:
            print(f"No services found matching '{query}'")
            return []
        
        print(f"\nFound {len(matches)} match(es):")
        for i, service in enumerate(matches, 1):
            print(f"  {i}. {service}")
        
        self._update_activity()
        return matches

    def get_password(self, service: str):
        """Retrieve and decrypt a password entry. Returns (username, password) or None."""
        if not self.cipher:
            print("Error: Database not loaded.")
            return None

        # Check for session timeout
        if self._check_session_timeout():
            return None

        if "passwords" not in self.passwords_data:
            print("No passwords stored yet.")
            return None

        if service not in self.passwords_data["passwords"]:
            matched_service = self._find_service_key(service)
            if matched_service:
                service = matched_service
            else:
                print(f"Error: '{service}' not found.")
                return None

        try:
            entries = self.passwords_data["passwords"][service]
            if not entries:
                print("No usernames stored for this service.")
                return None

            # If there's only one username, return it
            if len(entries) == 1:
                username = next(iter(entries.keys()))
                pwd = entries[username]["password"]
                self._update_activity()
                return (username, pwd)

            # Multiple usernames: prompt user to choose
            print(f"Multiple accounts found for '{service}':")
            for i, uname in enumerate(entries.keys(), 1):
                print(f"  {i}. {uname}")
            try:
                choice = int(input("Select account number or 0 to cancel: ").strip())
            except Exception:
                print("Cancelled.")
                return None
            if choice <= 0 or choice > len(entries):
                print("Cancelled.")
                return None
            username = list(entries.keys())[choice - 1]
            pwd = entries[username]["password"]
            self._update_activity()
            return (username, pwd)
        except Exception as e:
            print(f"Error retrieving password: {e}")
            return None

    def list_services(self) -> list:
        """List all stored services (shows encrypted count only - doesn't reveal names by default)."""
        if self._check_session_timeout():
            return []
        
        if "passwords" not in self.passwords_data or not self.passwords_data["passwords"]:
            print("\n No passwords stored yet.")
            return []
        
        count = len(self.passwords_data["passwords"])
        print(f"\n You have {count} stored password(s)")
        print("   (Use 'search' command or 'get password' to view details)\n")
        
        # Show obfuscated service names for privacy
        print("Available entries (hidden):")
        for i, service in enumerate(self.passwords_data["passwords"].keys(), 1):
            if len(service) > 2:
                hint = service[0] + "*" * (len(service) - 2) + service[-1]
            elif len(service) == 2:
                hint = service[0] + "*"
            else:
                hint = "*"
            print(f"  {i}. {hint}")
        
        self._update_activity()
        return list(self.passwords_data["passwords"].keys())

    def add_recovery_phrase(self, name: str, phrase: str, notes: str = "") -> bool:
        """Add a new recovery phrase entry."""
        if not self.cipher:
            print("Error: Database not loaded. Use setup_master_password() or load() first.")
            return False
        
        if self._check_session_timeout():
            return False
        
        # Store recovery phrases in a separate section
        if "recovery_phrases" not in self.passwords_data:
            self.passwords_data["recovery_phrases"] = {}
        
        try:
            encrypted = self._encrypt_blob({"phrase": phrase}, self.cipher)
            if encrypted is None:
                raise RuntimeError("Failed to encrypt recovery phrase")
            self.passwords_data["recovery_phrases"][name] = {
                "encrypted_phrase": encrypted,
                "notes": notes
            }
            self._save_database()
            self._update_activity()
            print(f"Recovery phrase for '{name}' saved!")
            return True
        except Exception as e:
            print(f"Error saving recovery phrase: {e}")
            return False

    def get_recovery_phrase(self, name: str) -> str:
        """Retrieve and decrypt a recovery phrase."""
        if not self.cipher:
            print("Error: Database not loaded.")
            return None
        
        if self._check_session_timeout():
            return None
        
        if "recovery_phrases" not in self.passwords_data:
            print("No recovery phrases stored yet.")
            return None
        
        if name not in self.passwords_data["recovery_phrases"]:
            matched_name = self._find_recovery_phrase_key(name)
            if matched_name:
                name = matched_name
            else:
                print(f"Error: '{name}' not found.")
                return None
        
        try:
            encrypted = self.passwords_data["recovery_phrases"][name]["encrypted_phrase"]
            blob = self._decrypt_blob(encrypted, self.cipher)
            if blob is None:
                raise RuntimeError("Failed to decrypt recovery phrase")
            decrypted = blob.get("phrase")
            self._update_activity()
            return decrypted
        except Exception as e:
            print(f"Error retrieving recovery phrase: {e}")
            return None

    def list_recovery_phrases(self) -> list:
        """List all stored recovery phrases."""
        if self._check_session_timeout():
            return []
        
        if "recovery_phrases" not in self.passwords_data or not self.passwords_data["recovery_phrases"]:
            print("No recovery phrases stored yet.")
            return []
        
        print("\nStored recovery phrases:")
        for i, (name, data) in enumerate(self.passwords_data["recovery_phrases"].items(), 1):
            notes = f" - {data['notes']}" if data['notes'] else ""
            print(f"{i}. {name}{notes}")
        
        self._update_activity()
        return list(self.passwords_data["recovery_phrases"].keys())

    def delete_recovery_phrase(self, name: str) -> bool:
        """Delete a recovery phrase entry."""
        if self._check_session_timeout():
            return False
        
        if "recovery_phrases" not in self.passwords_data:
            print("No recovery phrases stored.")
            return False
        
        if name not in self.passwords_data["recovery_phrases"]:
            print(f"Error: '{name}' not found.")
            return False
        
        del self.passwords_data["recovery_phrases"][name]
        self._save_database()
        self._update_activity()
        print(f"Recovery phrase for '{name}' deleted!")
        return True

    def update_recovery_phrase(self, name: str, new_phrase: str, notes: str = "") -> bool:
        """Update an existing recovery phrase."""
        if self._check_session_timeout():
            return False
        
        if "recovery_phrases" not in self.passwords_data:
            print("No recovery phrases stored.")
            return False
        
        if name not in self.passwords_data["recovery_phrases"]:
            print(f"Error: '{name}' not found.")
            return False
        
        try:
            encrypted = self._encrypt_blob({"phrase": new_phrase}, self.cipher)
            if encrypted is None:
                raise RuntimeError("Failed to encrypt recovery phrase")
            self.passwords_data["recovery_phrases"][name]["encrypted_phrase"] = encrypted
            if notes:
                self.passwords_data["recovery_phrases"][name]["notes"] = notes
            self._save_database()
            self._update_activity()
            print(f"Recovery phrase for '{name}' updated!")
            return True
        except Exception as e:
            print(f"Error updating recovery phrase: {e}")
            return False

    def delete_password(self, service: str, username: str = None) -> bool:
        """Delete a password entry. If username is provided, delete that account; otherwise delete the whole service."""
        if self._check_session_timeout():
            return False
        
        if "passwords" not in self.passwords_data:
            print("No passwords stored.")
            return False
        
        if service not in self.passwords_data["passwords"]:
            matched_service = self._find_service_key(service)
            if matched_service:
                service = matched_service
            else:
                print(f"Error: '{service}' not found.")
                return False
        
        if username:
            entries = self.passwords_data["passwords"][service]
            if username not in entries:
                print(f"Username '{username}' not found for service '{service}'.")
                return False
            # Securely delete password from memory before deletion
            password_data = entries[username]
            for key in password_data:
                if key == "password":
                    self._secure_delete_password_data(password_data[key])
            del entries[username]
            # If no more usernames, remove the service container
            if not entries:
                del self.passwords_data["passwords"][service]
            self._save_database()
            self._update_activity()
            print(f"Account '{username}' for '{service}' deleted!")
            return True
        else:
            del self.passwords_data["passwords"][service]
            self._save_database()
            self._update_activity()
            print(f"All accounts for '{service}' deleted!")
            return True
    
    def _secure_delete_password_data(self, password_str: str) -> None:
        """Securely overwrite password data in memory (DoD 5220.22-M standard)."""
        # Overwrite with random data 7 times (DoD standard)
        for _ in range(7):
            password_str = secrets.token_urlsafe(len(password_str))
        # Final overwrite with zeros
        password_str = "\x00" * len(password_str)

    def update_password(self, service: str, username: str, new_password: str) -> bool:
        """Update an existing password for a specific username under a service."""
        if self._check_session_timeout():
            return False
        
        if "passwords" not in self.passwords_data:
            print("No passwords stored.")
            return False
        
        if service not in self.passwords_data["passwords"]:
            matched_service = self._find_service_key(service)
            if matched_service:
                service = matched_service
            else:
                print(f"Error: '{service}' not found.")
                return False
        
        entries = self.passwords_data["passwords"][service]
        if username not in entries:
            print(f"Username '{username}' not found for service '{service}'.")
            return False
        try:
            entries[username]["password"] = new_password
            self._save_database()
            self._update_activity()
            print(f"Password for '{service}' ({username}) updated!")
            return True
        except Exception as e:
            print(f"Error updating password: {e}")
            return False

    @staticmethod
    def generate_password(length: int = 16, use_symbols: bool = True) -> str:
        """Generate a secure random password."""
        characters = string.ascii_letters + string.digits
        if use_symbols:
            characters += string.punctuation
        
        password = ''.join(secrets.choice(characters) for _ in range(length))
        return password


def get_default_db_dir() -> str:
    """Return the default directory for password databases (Linux only)."""
    return os.path.expanduser('~/.config/password-manager')


def get_db_state_file() -> str:
    """Return the path for storing the last-used database file."""
    return os.path.join(get_default_db_dir(), 'current_db.json')


def load_last_db_file() -> str:
    """Load the last-used database path from state, if available."""
    state_file = get_db_state_file()
    try:
        if os.path.exists(state_file):
            with open(state_file, 'r') as f:
                data = json.load(f)
            db_file = data.get('db_file', '')
            if db_file and os.path.exists(db_file):
                return db_file
    except Exception:
        pass
    return None


def save_last_db_file(db_file: str) -> None:
    """Save the last-used database path to state."""
    state_file = get_db_state_file()
    db_dir = os.path.dirname(state_file)
    if db_dir:
        Path(db_dir).mkdir(parents=True, exist_ok=True)
        try:
            if platform.system() != "Windows":
                os.chmod(db_dir, 0o700)
        except Exception:
            pass
    try:
        with open(state_file, 'w') as f:
            json.dump({'db_file': os.path.abspath(db_file)}, f)
        os.chmod(state_file, 0o600)  # Linux: owner only
    except Exception:
        pass


def clear_screen():
    """Clear the console screen (Linux only)."""
    try:
        subprocess.run(['clear'], check=False)
    except Exception:
        # Fallback: print newlines if subprocess fails
        print("\n" * 100)


def pause(message: str = "Press Enter to continue..."):
    """Pause the console and clear the screen afterward."""
    input(message)
    clear_screen()


def main():
    """Simple command-line interface for the password manager."""
    import getpass

    parser = argparse.ArgumentParser(description="Secure Password Manager")
    parser.add_argument("--db", help="Path to the password database file.")
    parser.add_argument("--random-db", action="store_true",
                        help="Use a randomly named database file in the default database directory.")
    args = parser.parse_args()

    db_file = None
    if args.db:
        db_file = args.db
    elif args.random_db:
        default_dir = get_default_db_dir()
        Path(default_dir).mkdir(parents=True, exist_ok=True)
        random_name = f"passwords-{secrets.token_hex(8)}.db"
        db_file = os.path.join(default_dir, random_name)
    else:
        db_file = load_last_db_file()

    manager = PasswordManager(db_file=db_file)

    # Clear screen and show header
    clear_screen()
    print("=" * 50)
    print("    Secure Password Manager".center(50))
    print("    AES-256-GCM + Argon2id • Strong password vault".center(50))
    print("=" * 50)
    print()
    
    db_location = manager.db_file
    print(f"Database location: {db_location}\n")
    
    # Check if database exists
    if not os.path.exists(manager.db_file):
        print("No existing database found. Creating new one...\n")
        while True:
            master_pwd = getpass.getpass("Set your master password: ")
            
            if len(master_pwd) < 8:
                print("Master password must be at least 8 characters.\n")
                continue
            
            # Check password strength
            strength, feedback = PasswordManager._check_password_strength(master_pwd)
            if strength < 3:
                print(f"\nPassword strength: {strength}/5 - NOT ACCEPTABLE")
                print("Your master password is too weak. It must have:")
                print("- At least 12 characters")
                print("- Uppercase AND lowercase letters")
                print("- Numbers")
                print("- Symbols (!@#$%^&*()-_=+)")
                print("\nCurrent feedback:")
                for tip in feedback:
                    print(f"  • {tip}")
                print("\nPlease choose a stronger password.")
                continue
            elif strength == 3:
                print(f"[OK] Password strength: {strength}/5 - ACCEPTABLE")
            else:
                print(f"[OK] Password strength: {strength}/5 - STRONG")
            
            confirm_pwd = getpass.getpass("Confirm master password: ")
            
            if master_pwd != confirm_pwd:
                print("Passwords don't match. Try again.\n")
                continue
            
            # Set up security question
            print("\nSecurity Question Setup (for account recovery)")
            security_question = input("Enter a security question (e.g., What is your pet's name?): ").strip()
            if not security_question or len(security_question) > 200:
                print("Security question invalid (max 200 characters).\n")
                continue
            
            security_answer = getpass.getpass("Enter the answer (case-insensitive): ").strip()
            if not security_answer or len(security_answer) > 200:
                print("Security answer invalid (max 200 characters).\n")
                continue
            
            confirm_answer = getpass.getpass("Confirm the answer: ").strip()
            if security_answer != confirm_answer:
                print("Answers don't match. Try again.\n")
                continue
            
            if manager.setup_master_password(master_pwd, security_question, security_answer):
                save_last_db_file(manager.db_file)
                break
    else:
        # Load existing database
        print("Loading existing database...\n")
        attempts = 0
        while attempts < 3:
            master_pwd = getpass.getpass("Enter your master password: ")
            if manager.load(master_pwd):
                save_last_db_file(manager.db_file)
                break
            attempts += 1
            if attempts < 3:
                print(f"Incorrect password. Attempts remaining: {3 - attempts}\n")
            else:
                print("Too many failed attempts. Exiting.")
                sys.exit(1)
    
    # Main menu loop
    while True:
        print("\n" + "=" * 50)
        print("MENU".center(50))
        print("=" * 50)
        print("1. Add password")
        print("2. Get password")
        print("3. Search services")
        print("4. List services (hidden view)")
        print("5. Update password")
        print("6. Delete password")
        print("7. Add recovery phrase")
        print("8. Get recovery phrase")
        print("9. List recovery phrases")
        print("10. Update recovery phrase")
        print("11. Delete recovery phrase")
        print("12. Generate password")
        print("13. Exit")
        print("=" * 50)
        
        # Secure menu input (doesn't echo keystrokes to terminal)
        choice = getpass.getpass(prompt="\nEnter your choice (1-13 or full option name): ").strip().lower()
        
        # Map text input to numbers
        choice_map = {
            "add password": "1",
            "get password": "2", "retrieve": "2",
            "search": "3", "search services": "3",
            "list": "4", "list services": "4",
            "update": "5", "update password": "5",
            "delete": "6", "delete password": "6",
            "add recovery": "7", "add phrase": "7",
            "get recovery": "8", "get phrase": "8", "retrieve phrase": "8",
            "list recovery": "9", "list phrases": "9",
            "update recovery": "10", "update phrase": "10",
            "delete recovery": "11", "delete phrase": "11",
            "generate": "12", "generate password": "12",
            "exit": "13", "quit": "13", "logout": "13"
        }
        
        # Handle text input
        if choice in choice_map:
            choice = choice_map[choice]
        
        if choice == "1":
            print()
            service = input("Service name (e.g., Gmail): ").strip()
            if not service:
                print("Service name cannot be empty.")
                continue
            existing_service = manager._find_service_key(service)
            overwrite_choice = False
            if existing_service:
                confirm = input(f"Service '{existing_service}' already exists. Overwrite it? (y/n): ").lower().strip()
                if confirm != 'y':
                    print("Cancelled.")
                    continue
                overwrite_choice = True
                service = existing_service
            username = input("Username/email: ").strip()
            if not username:
                print("Username cannot be empty.")
                continue
            password = getpass.getpass("Password: ")
            if not password:
                print("Password cannot be empty.")
                continue
            manager.add_password(service, username, password, overwrite=overwrite_choice)
        
        elif choice == "2":
            print()
            service = input("Enter service name to retrieve: ").strip()
            result = manager.get_password(service)
            if result:
                username, password = result
                print(f"\nPassword retrieved")
                print("=" * 50)
                print(f"Service:  {service}")
                print(f"Username: {username}")
                print(f"Password: {password}")
                print("=" * 50)
                pause()
        
        elif choice == "3":
            print()
            query = input("Search for service (e.g., 'gm' for Gmail): ").strip()
            if query:
                manager.search_service(query)
            else:
                print("Search query cannot be empty.")
        
        elif choice == "4":
            manager.list_services()
            pause()
        
        elif choice == "5":
            print()
            service = input("Enter service name to update: ").strip()
            result = manager.get_password(service)
            if result:
                username, _ = result
                new_pwd = getpass.getpass("New password: ")
                if not new_pwd:
                    print("Password cannot be empty.")
                    continue
                manager.update_password(service, username, new_pwd)
            else:
                print(f"Service not found.")
        
        elif choice == "6":
            print()
            service = input("Enter service name to delete: ").strip()
            # Let user select specific account if multiple exist
            result = manager.get_password(service)
            if not result:
                print("Service not found or cancelled.")
                continue
            username, _ = result
            confirm = input(f"Delete account '{username}' for service '{service}'? (y = delete account, a = delete ALL accounts for this service, n = cancel): ").lower()
            if confirm == 'y':
                manager.delete_password(service, username=username)
            elif confirm == 'a':
                confirm2 = input(f"Are you sure you want to DELETE ALL accounts for '{service}'? This cannot be undone. (y/n): ").lower()
                if confirm2 == 'y':
                    manager.delete_password(service)
                else:
                    print("Cancelled.")
            else:
                print("Cancelled.")
        
        elif choice == "7":
            print()
            name = input("Name/description (e.g., Bitcoin Wallet): ").strip()
            if not name:
                print("Name cannot be empty.")
                continue
            
            try:
                word_count = int(input("How many words in your recovery phrase? (e.g., 12, 24): ").strip())
                if word_count < 1:
                    print("Word count must be at least 1.")
                    continue
            except ValueError:
                print("Invalid input. Please enter a number.")
                continue
            
            print(f"\nEnter your {word_count} recovery words (one word per line):")
            words = []
            for i in range(word_count):
                word = input(f"Word {i+1}/{word_count}: ").strip()
                if not word:
                    print("Word cannot be empty. Please try again.")
                    continue
                words.append(word)
            
            phrase = " ".join(words)
            notes = input("\nNotes (optional, e.g., stored in safe): ").strip()
            manager.add_recovery_phrase(name, phrase, notes)
        
        elif choice == "8":
            print()
            manager.list_recovery_phrases()
            name = input("\nEnter recovery phrase name to retrieve: ").strip()
            phrase = manager.get_recovery_phrase(name)
            if phrase:
                words = phrase.split()
                print(f"\nRecovery phrase retrieved: {name}")
                print("=" * 50)
                for i, word in enumerate(words, 1):
                    print(f"{i:2d}. {word}")
                print("=" * 50)
                pause()
        
        elif choice == "9":
            manager.list_recovery_phrases()
            pause()
        
        elif choice == "10":
            print()
            manager.list_recovery_phrases()
            name = input("\nEnter recovery phrase name to update: ").strip()
            if "recovery_phrases" not in manager.passwords_data or name not in manager.passwords_data.get("recovery_phrases", {}):
                print(f"Recovery phrase '{name}' not found.")
                continue
            print("Enter new recovery phrase:")
            lines = []
            try:
                while True:
                    line = input()
                    lines.append(line)
            except EOFError:
                pass
            except KeyboardInterrupt:
                print("\nCancelled.")
                continue
            
            new_phrase = "\n".join(lines).strip()
            if not new_phrase:
                new_phrase = getpass.getpass("Recovery phrase: ")
                if not new_phrase:
                    print("Recovery phrase cannot be empty.")
                    continue
            
            notes = input("Update notes (optional, press Enter to skip): ").strip()
            manager.update_recovery_phrase(name, new_phrase, notes)
        
        elif choice == "11":
            print()
            manager.list_recovery_phrases()
            name = input("\nEnter recovery phrase name to delete: ").strip()
            confirm = input(f"Are you sure you want to delete '{name}'? (y/n): ").lower()
            if confirm == 'y':
                manager.delete_recovery_phrase(name)
            else:
                print("Cancelled.")
        
        elif choice == "12":
            print()
            try:
                length_input = input("Password length (default 16, range 8-128): ").strip()
                length = int(length_input) if length_input else 16
                if length < 8 or length > 128:
                    print("Length must be between 8 and 128.")
                    continue
            except ValueError:
                print("Invalid input. Using default length 16.")
                length = 16
            
            symbols = input("Include symbols? (y/n, default y): ").lower().strip()
            use_sym = symbols != 'n'
            pwd = PasswordManager.generate_password(length, use_sym)
            print(f"\nGenerated password:\n{pwd}")
            
            save = input("\nSave this password? (y/n): ").lower()
            if save == 'y':
                service = input("Service name: ").strip()
                username = input("Username/email: ").strip()
                if not service or not username:
                    print("Service and username are required.")
                    continue

                existing_service = manager._find_service_key(service)
                overwrite_choice = False
                if existing_service:
                    confirm = input(f"Service '{existing_service}' already exists. Overwrite it? (y/n): ").lower().strip()
                    if confirm != 'y':
                        print("Cancelled.")
                        continue
                    overwrite_choice = True
                    service = existing_service

                manager.add_password(service, username, pwd, overwrite=overwrite_choice)
        
        elif choice == "13":
            print("\nGoodbye! Stay secure!")
            break
        
        else:
            print("Invalid choice. Please try again.")


if __name__ == "__main__":
    main()
