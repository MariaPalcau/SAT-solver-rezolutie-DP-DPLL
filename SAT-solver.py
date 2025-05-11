import time
import os
import random
try:
    from pysat.solvers import Solver
    PYSAT_AVAILABLE = True
except ImportError:
    PYSAT_AVAILABLE = False
    print("Avertisment: PySAT nu este disponibil. Validarea va fi dezactivata.")

#Citeste un fisier DIMACS si returneaza clauzele si numarul de variabile
def parse_dimacs(filename):
    clauses = []
    with open(filename) as file:
        for line in file:
            if line.startswith(('c', '%')) or line.strip() == '': 
                continue
            if line.startswith('p'):
                nvars, nclauses = line.split()[2:4]
                continue
            literals = [int(x) for x in line.split() if int(x) != 0]
            if literals: 
                clauses.append(frozenset(literals))
    return clauses, int(nvars)

#Genereaza clauze CNF aleatorii cu dimensiuni variabile
def generate_random_clauses(num_vars, num_clauses, min_clause_size=1, max_clause_size=5):
    clauses = []
    for _ in range(num_clauses):
        size = random.randint(min_clause_size, min(max_clause_size, num_vars))
        vars_in_clause = random.sample(range(1, num_vars + 1), size)
        clause = frozenset(var * random.choice([-1, 1]) for var in vars_in_clause)
        clauses.append(clause)
    return clauses

#Verifica daca o clauza este o tautologie
def is_tautology(clause):
    return any(-lit in clause for lit in clause)

#Elimina clauzele tautologice din formula
def remove_tautologies(cnf):
    return set([cl for cl in cnf if not is_tautology(cl)])

#Elimina clauzele subsumate din formula CNF
def apply_subsumption(cnf):
    cnf = list(cnf)
    subsumed = set()
    for i in range(len(cnf)):
        for j in range(len(cnf)):
            if i != j and cnf[i].issubset(cnf[j]):
                subsumed.add(cnf[j])
    return set(cnf) - subsumed

#Rezolutia
def resolve_on(p, cnf, max_clauses, start_time, max_time):
    if start_time is None:
        start_time = time.perf_counter()
    if time.perf_counter() - start_time > max_time:
        return None

    pos_p = [c - {p} for c in cnf if p in c]
    neg_p = [c - {-p} for c in cnf if -p in c]
    no_p = [c for c in cnf if p not in c and -p not in c]

    new_clauses = set(no_p)

    for c1 in pos_p:
        for c2 in neg_p:
            res = frozenset(c1 | c2)
            if is_tautology(res):
                continue
            if any(res.issuperset(c) for c in new_clauses):
                continue 
            new_clauses = {c for c in new_clauses if not c.issuperset(res)}
            new_clauses.add(res)
            if len(new_clauses) > max_clauses:
                raise MemoryError(f"[Eroare] S-a depasit numarul maxim de clauze permis: {max_clauses}")
            if time.perf_counter() - start_time > max_time:
                return None
    return new_clauses

#Aplica regula clauzei cu un literal
def one_literal(cnf):
    for clause in cnf:
        if len(clause) == 1:
            lit = next(iter(clause))
            new_cnf = set()
            for c in cnf:
                if lit in c:
                    continue
                new_clause = c - {-lit}
                if new_clause == set():
                    return set([frozenset()])
                new_cnf.add(frozenset(new_clause))
            return new_cnf
    return None

#Elimina clauzele ce contin literali puri
def pure_literal(cnf):
    literals = set(l for clause in cnf for l in clause)
    pure_literals = {l for l in literals if -l not in literals}
    if not pure_literals:
        return None
    return set(clause for clause in cnf if clause.isdisjoint(pure_literals))

#Algoritm Davis-Putnam
def dp_solver(cnf, method, max_time=60, max_clauses=100000):
    start_time = time.perf_counter()
    cnf = apply_subsumption(cnf)
    while cnf:
        if time.perf_counter() - start_time > max_time:
            return None
        if len(cnf) > max_clauses:
            return None
        if frozenset() in cnf:
            return False
        cnf1 = remove_tautologies(cnf)
        if cnf1 != cnf:
            cnf = cnf1
            continue
        if method == "dp":
            cnf1 = one_literal(cnf)
            if cnf1 is not None:
                cnf = cnf1
                continue
        if method == "dp":
            cnf1 = pure_literal(cnf)
            if cnf1 is not None:
                cnf = cnf1
                continue
        p = next(iter(next(iter(cnf))))
        cnf = resolve_on(p, cnf, max_clauses, start_time, max_time)
        if cnf is None:
            return None
        cnf = apply_subsumption(cnf)
    return True


#Functii pentru algortimul DPLL

#Numara aparitiile fiecarui literal in formula
def get_counter(formula):
    counter = {}
    for clause in formula:
        for literal in clause:
            if literal in counter:
                counter[literal] += 1
            else:
                counter[literal] = 1
    return counter

#Simplifica formula folosind variabilele deja atribuite
def simplify(formula, assignment):
    simplified = []
    assigned = set(assignment)
    for clause in formula:
        if any(lit in assigned for lit in clause):
            continue
        new_clause = [lit for lit in clause if -lit not in assigned]
        if not new_clause:
            return -1
        simplified.append(new_clause)
    return simplified

#Propagare unitatii
def unit_propagation(formula):
    assignment = []
    if formula == -1:
        return formula, assignment
    unit_clauses = [clause for clause in formula if len(clause) == 1]
    while unit_clauses:
        unit = unit_clauses[0][0]
        assignment.append(unit)
        formula = simplify(formula, [unit])
        if formula == -1:
            return formula, assignment
        unit_clauses = [clause for clause in formula if len(clause) == 1]
    return formula, assignment

#Elimina literalii puri din formula
def pure_literal_elimination(formula):
    counter = get_counter(formula)
    assignment = []
    pures = []
    for literal in counter:
        if -literal not in counter:
            pures.append(literal)
    for pure in pures:
        assignment.append(pure)
    if pures:
        formula = simplify(formula, pures)
    return formula, assignment

#Alege variabila folosind euristica MOM (Maximum Occurrences in Minimum-size clauses)
def mom_heuristic(formula):
    if not formula:
        return None
    min_len = min(len(clause) for clause in formula)
    short_clauses = [clause for clause in formula if len(clause) == min_len]
    literal_count = get_counter(short_clauses)
    variable_scores = {}
    for literal in literal_count:
        var = abs(literal)
        pos = literal_count.get(var, 0)
        neg = literal_count.get(-var, 0)
        score = (pos + neg) * (2 ** min_len) + (pos * neg)
        variable_scores[var] = score
    
    return max(variable_scores, key=variable_scores.get)

#DPLL
def dpll(formula, start_time, max_time, assignment=None):
    if start_time is None:
        start_time = time.perf_counter()
    if max_time is not None and time.perf_counter() - start_time > max_time:
        return -1
    if assignment is None:
        assignment = []
    formula, unit_assignment = unit_propagation(formula)
    if formula == -1:
        return []
    assignment += unit_assignment
    formula, pure_assignment = pure_literal_elimination(formula)
    if formula == -1:
        return []
    assignment += pure_assignment
    if not formula:
        return assignment
    var = mom_heuristic(formula)
    if var is None:
        return assignment
    for val in [var, -var]:
        new_formula = simplify(formula, [val])
        if new_formula != -1:
            result = dpll(new_formula, start_time, max_time, assignment + [val])
            if result:
                return result
    if max_time is not None and time.perf_counter() - start_time > max_time:
        return -1
    return []

#Valideaza satisfiabilitatea formulei folosind PySAT
def check_with_pysat(clauses):
    if not PYSAT_AVAILABLE:
        print("PySAT nu este disponibil pentru validare")
        return None
    int_clauses = [list(cl) for cl in clauses]
    with Solver(bootstrap_with=int_clauses) as solver:
        return solver.solve()


def main():
    mode = input("Alege modul de intrare: pentru F (fisier) sau R (random)? ").strip().lower()
    if mode == 'f':
        filename = input("Introdu calea catre fisierul .cnf: ").strip()
        if not os.path.exists(filename):
            print(f"Fisierul '{filename}' nu exista.")
            return
        clauses, nvars = parse_dimacs(filename)
    elif mode == 'r':
        try:
            num_vars = int(input("Numar de variabile: "))
            num_clauses = int(input("Numar de clauze: "))
            min_clause_size = int(input("Dimensiune minima clauza (default 3): ") or 3)
            max_clause_size = int(input("Dimensiune maxima clauza (default 3): ") or 3)
        except ValueError:
            print("Valori invalide. Se folosesc valorile implicite: 20 variabile, 50 clauze, dimensiune 3")
            num_vars, num_clauses, min_clause_size, max_clause_size = 20, 50, 3, 3
        
        clauses = generate_random_clauses(num_vars, num_clauses, min_clause_size, max_clause_size)
        nvars = num_vars
        print(f"Au fost generate {len(clauses)} clauze aleatorii")
        for clause in clauses: 
            print(list(clause))
    else:
        print("Mod de intrare invalid. Alege 'F' sau 'R'.")
        return
    
    method = input("Alege metoda de rezolvare (rezolutie / dp / dpll): ").strip().lower()
    if method not in {"dp", "rezolutie", "dpll"}:
        print("Metoda invalida.")
        return
    
    max_time = 60 
    max_clauses = 100000
    
    if method in ["dp", "rezolutie"]:
        try:
            max_time = int(input("Timp maxim de executie (secunde): "))
            max_clauses = int(input("Numar maxim permis de clauze: "))
        except ValueError:
            print("Se folosesc limitele implicite de timp si clauze")
    
    check_pysat_flag = input("Validare cu PySAT? (da/nu): ").strip().lower() in {"da"}
    if check_pysat_flag and not PYSAT_AVAILABLE:
        print("PySAT nu este disponibil. Validarea va fi omisa.")
        check_pysat_flag = False
    
    if method == "dpll":
        try:
            max_time = int(input("Timp maxim de executie (secunde): "))
        except ValueError:
            print("Valoare invalida. Se foloseste timeout implicit de 60 secunde.")
            max_time = 60.0
        start = time.perf_counter()
        dpll_clauses = [list(cl) for cl in clauses]
        solution = dpll(dpll_clauses, start, max_time, [])
        elapsed = time.perf_counter() - start
        
        if isinstance(solution, list) and solution:
            solution += [x for x in range(1, nvars + 1) if x not in solution and -x not in solution]
            solution.sort(key=lambda x: abs(x))
            print("s SATISFIABLE")
            print("v", ' '.join([str(x) for x in solution]))
        elif solution == []:
            print("s UNSATISFIABLE")
        elif solution == -1:
            print("S-a depasit timpul limita.")
        print(f"Timp: {elapsed:.4f} secunde")
    else:
        start = time.perf_counter()
        result = dp_solver(set(clauses), method=method, max_time=max_time, max_clauses=max_clauses)
        elapsed = time.perf_counter() - start
        
        if result is None:
            print("S-a depasit timpul sau numarul de clauze.")
        elif result:
            print("s SATISFIABLE")
        else:
            print("s UNSATISFIABLE")
        print(f"Timp: {elapsed:.4f} secunde")
    if check_pysat_flag:
        print("Se valideaza cu PySAT...")
        pysat_result = check_with_pysat(clauses)
        print("PySAT:", "s SATISFIABLE" if pysat_result else "s UNSATISFIABLE")

if __name__ == '__main__':
    main()