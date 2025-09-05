# 1 Threshold decryption
# 2 Distributed key generation
# 3 


import random
from math import gcd
import sympy
import hashlib

# Paillier Implementation
def mod_inverse(a, m):
    return pow(a, -1, m)

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

class PaillierPriv:
    def __init__(self, lam):
        self.lam = lam

def generate_paillier(bits):
    p = int(sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2))))
    q = int(sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2))))
    while p == q:
        q = int(sympy.nextprime(random.randint(2**(bits//2 - 1), 2**(bits//2))))
    n = p * q
    g = n + 1
    lam = sympy.lcm(p-1, q-1)
    pub = PaillierPub(n, g)
    priv = PaillierPriv(int(lam))
    return pub, priv

def L(u, n):
    return (u - 1) // n

def decrypt(c, pub, priv):
    n2 = pub.n2
    u = pow(c, priv.lam, n2)
    l = L(u, pub.n)
    mu = mod_inverse(L(pow(pub.g, priv.lam, n2), pub.n), pub.n)
    return (l * mu) % pub.n

def add(pub, c1, c2):
    return (c1 * c2) % pub.n2

def homomorphic_add(pub, enc_list):
    enc_sum = 1
    for enc in enc_list:
        enc_sum = add(pub, enc_sum, enc)
    return enc_sum

# Hash function for personnummer
def hash_id(personnummer, salt="global_salt"):
    return hashlib.sha256((str(personnummer) + salt).encode()).hexdigest()[:10]

# Simulation Parameters
NUM_BANKS = 5
CLIENTS_PER_BANK = 1000
OVERLAP_PERCENT = 0.15
PERSONNUMMER_RANGE = 6000  # Increased for better overlap
THRESHOLD = 70
BITS = 512

# Generate global keys
pub, priv = generate_paillier(BITS)

class Bank:
    def __init__(self, id, priv):
        self.id = id
        self.priv = priv
        self.clients = {}  # {personnummer: risk_score}

    def generate_clients(self, all_personnummer):
        print("===Generating clients (~1000 each bank)")
        num_clients = random.randint(900, 1100)
        selected_pn = random.sample(all_personnummer, k=num_clients)  # Unique within bank
        self.clients = {pn: random.randint(1, 100) for pn in selected_pn}  # Adjusted range for >70 avgs

    def encrypt_scores(self, pub):
        return {hash_id(cid): pub.encrypt(score) for cid, score in self.clients.items()}

    def decrypt_and_check(self, pub, pseudo_id, enc_sum, count):
        if count == 0:
            return pseudo_id, pub.encrypt(0)
        sum_risk = decrypt(enc_sum, pub, self.priv)
        avg = sum_risk / count
        flag = 1 if avg > THRESHOLD else 0
        return pseudo_id, pub.encrypt(flag)

class Server:
    def __init__(self, pub):
        self.pub = pub
        self.all_data = {}  # {hashed_id: [enc_risk from banks]}
        self.counts = {}  # {hashed_id: count}
        self.id_mapping = {}  # {hashed_id: set(personnummer)} - Use set for multiple mappings

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
            pseudo_id_resp, enc_flag = bank.decrypt_and_check(self.pub, pseudo_id, enc_sum, count)
            responses[pseudo_id_resp] = (hashed_id, enc_flag)
            bank_index += 1

        self.flags = {hashed_id: enc_flag for pseudo_id, (hashed_id, enc_flag) in responses.items()}  # Key by hashed_id temporarily


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
    banks = [Bank(i, priv) for i in range(NUM_BANKS)]
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

    # Find a flagged example
    for pn in banks[0].clients:
        hashed_id = hash_id(pn)
        if hashed_id in server.flags:
            enc_flag = server.flags[hashed_id]
            flag = decrypt(enc_flag, pub, priv)
            print(f"Example: Personnummer {pn} flag: {flag} (1 if avg > {THRESHOLD})")
            break

simulate()
