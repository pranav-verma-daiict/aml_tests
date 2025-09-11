# the distributed key generation using BD scheme
# the decryption requires contribution from everyone (all 5 banks)


# todo: remove server and make it fully distributed
import random
from math import gcd
import sympy
import hashlib

# Utility Functions
def lcm(a, b):
    return a * b // gcd(a, b)

def mod_inverse(a, m):
    try:
        return pow(a, -1, m)
    except ValueError:
        raise ValueError("Modular inverse does not exist")

def L(u, n):
    return (u - 1) // n

# Paillier Implementation
class PaillierPub:
    def __init__(self, n, g):
        self.n = n
        self.g = g
        self.n2 = n * n

    def encrypt(self, m):
        assert 0 <= m < self.n, "Message out of range"
        while True:
            r = random.randint(1, self.n - 1)
            if gcd(r, self.n) == 1:
                break
        return (pow(self.g, m, self.n2) * pow(r, self.n, self.n2)) % self.n2

def collective_decrypt(c, shares, n, g):
    n2 = n * n
    u = 1
    for share in shares:
        u = (u * pow(c, share, n2)) % n2
    lam = sum(shares)
    mu = mod_inverse(L(pow(g, lam, n2), n), n)
    l = L(u, n)
    return (l * mu) % n

def add(pub, c1, c2):
    return (c1 * c2) % pub.n2

def homomorphic_add(pub, enc_list):
    enc_sum = 1
    for enc in enc_list:
        enc_sum = add(pub, enc_sum, enc)
    return enc_sum

# Burmester-Desmedt Group Key Exchange
def bd_key_exchange(n_parties, p, g):
    # Round 1: Each bank picks secret and broadcasts z_i
    secrets = [random.randint(1, p-2) for _ in range(n_parties)]
    z = [pow(g, x, p) for x in secrets]
    
    # Round 2: Compute and broadcast X_i
    X = []
    for i in range(n_parties):
        i_prev = (i - 1) % n_parties
        i_next = (i + 1) % n_parties
        numerator = (z[i_next] * mod_inverse(z[i_prev], p)) % p
        X_i = pow(numerator, secrets[i], p)
        X.append(X_i)
    
    # Compute shared key K for each bank
    K_list = []
    for i in range(n_parties):
        i_prev = (i - 1) % n_parties
        prod = pow(z[i_prev], n_parties * secrets[i], p)
        for j in range(1, n_parties):
            prod = (prod * pow(X[(i + j - 1) % n_parties], n_parties - j, p)) % p
        K_list.append(prod)
    
    # Verify all keys are the same
    K = K_list[0]
    assert all(k == K for k in K_list), "BD keys differ"
    return K, secrets

# Generate Paillier keys from BD shared secret
def generate_paillier_from_seed(K, bits):
    # Deterministic prime generation from K
    seed = int(hashlib.sha256(str(K).encode()).hexdigest(), 16)
    random.seed(seed)
    
    p = sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2)))
    q = sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2)))
    while p == q or gcd(p * q, (p-1) * (q-1)) != 1:
        q = sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2)))
    n = p * q
    g = n + 1
    lam = lcm(p-1, q-1)
    return n, g, lam

# Hash function for personnummer
def hash_id(personnummer, salt="global_salt"):
    return hashlib.sha256((str(personnummer) + salt).encode()).hexdigest()[:10]

# Simulation Parameters
NUM_BANKS = 5
CLIENTS_PER_BANK = 1000
OVERLAP_PERCENT = 0.15
PERSONNUMMER_RANGE = 6000
THRESHOLD = 70
BITS = 512
BD_P = sympy.nextprime(random.randint(2**BITS, 2**(BITS+1)))
BD_G = 2

class Bank:
    def __init__(self, id, lam_share):
        self.id = id
        self.lam_share = lam_share  # Private key share
        self.clients = {}

    def generate_clients(self, all_personnummer):
        print(f"===Generating clients for Bank {self.id} (~1000)===")
        num_clients = random.randint(900, 1100)
        selected_pn = random.sample(all_personnummer, k=num_clients)
        self.clients = {pn: random.randint(1, 100) for pn in selected_pn}

    def encrypt_scores(self, pub):
        return {hash_id(cid): pub.encrypt(score) for cid, score in self.clients.items()}

    def decrypt_and_check(self, pub, pseudo_id, enc_sum, count, all_shares):
        if count == 0:
            return pseudo_id, pub.encrypt(0)
        sum_risk = collective_decrypt(enc_sum, all_shares, pub.n, pub.g)
        avg = sum_risk / count
        flag = 1 if avg > THRESHOLD else 0
        return pseudo_id, pub.encrypt(flag)

class Server:
    def __init__(self, pub):
        self.pub = pub
        self.all_data = {}  # {hashed_id: [enc_risk]}
        self.counts = {}    # {hashed_id: count}
        self.id_mapping = {}  # {hashed_id: set(personnummer)}

    def receive_data(self, bank_id, data):
        for hashed_id, enc_risk in data.items():
            if hashed_id not in self.all_data:
                self.all_data[hashed_id] = []
                self.counts[hashed_id] = 0
                self.id_mapping[hashed_id] = set()
            self.all_data[hashed_id].append(enc_risk)
            self.counts[hashed_id] += 1

    def aggregate(self):
        print("===Computing aggregate for all clients===")
        for hashed_id in self.all_data:
            self.all_data[hashed_id] = homomorphic_add(self.pub, self.all_data[hashed_id])

    def distribute_for_check(self, banks):
        hashed_ids = list(self.all_data.keys())
        random.shuffle(hashed_ids)
        tasks_per_bank = (len(hashed_ids) + NUM_BANKS - 1) // NUM_BANKS
        assignments = [hashed_ids[i * tasks_per_bank:(i + 1) * tasks_per_bank] for i in range(NUM_BANKS)]

        responses = {}
        bank_index = 0
        for hashed_id in hashed_ids:
            bank = banks[bank_index % NUM_BANKS]
            pseudo_id = random.randint(100000, 999999)
            enc_sum = self.all_data[hashed_id]
            count = self.counts[hashed_id]
            # Collect all lam_shares for decryption
            all_shares = [b.lam_share for b in banks]
            pseudo_id_resp, enc_flag = bank.decrypt_and_check(self.pub, pseudo_id, enc_sum, count, all_shares)
            responses[pseudo_id_resp] = (hashed_id, enc_flag)
            bank_index += 1

        self.flags = {hashed_id: enc_flag for pseudo_id, (hashed_id, enc_flag) in responses.items()}

    def send_flags_to_banks(self, banks):
        for bank in banks:
            bank_flags = {}
            for pn in bank.clients:
                hashed_id = hash_id(pn)
                if hashed_id in self.flags:
                    bank_flags[pn] = self.flags[hashed_id]
            print(f"Bank {bank.id} receives flags for its clients: {len(bank_flags)} entries")

# Simulation
def simulate():
    all_personnummer = list(range(1000000000, 1000000000 + PERSONNUMMER_RANGE))
    
    # Run BD key exchange
    print("===Running Burmester-Desmedt Group Key Exchange===")
    K, secrets = bd_key_exchange(NUM_BANKS, BD_P, BD_G)
    print(f"Shared secret K from BD: {K}")
    
    # Generate Paillier keys from K
    n, g, lam = generate_paillier_from_seed(K, BITS)
    pub = PaillierPub(n, g)
    
    # Distribute lam as additive shares
    lam_shares = [random.randint(0, lam // NUM_BANKS) for _ in range(NUM_BANKS - 1)]
    lam_shares.append(lam - sum(lam_shares))  # Ensure sum = lam
    
    banks = [Bank(i, lam_shares[i]) for i in range(NUM_BANKS)]
    for bank in banks:
        bank.generate_clients(all_personnummer)
        print(f"Total clients at Bank {bank.id}: {len(bank.clients)}")

    server = Server(pub)

    for bank in banks:
        enc_data = bank.encrypt_scores(pub)
        server.receive_data(bank.id, enc_data)

    server.aggregate()
    server.distribute_for_check(banks)
    server.send_flags_to_banks(banks)

    # Test example with known client
    for pn in banks[0].clients:
        hashed_id = hash_id(pn)
        if hashed_id in server.flags:
            enc_flag = server.flags[hashed_id]
            flag = collective_decrypt(enc_flag, lam_shares, n, g)
            print(f"Example: Personnummer {pn} flag: {flag} (1 if avg > {THRESHOLD})")
            break

if __name__ == "__main__":
    simulate()
