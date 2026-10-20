-- Prove2me | solution 1 for GoldbachSieve.survivor_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:39:48.850595+00:00
-- url     : https://prove2.me/submissions/b000da9c-2125-4d20-869d-e98bd0f05fc1

import Definitions.Def_GoldbachSieve
import Theorems.Thm_GoldbachSieve_mem_survivors

open GoldbachSieve

theorem solution {lo hi c q : ℕ} (hq : q.Prime)
    (h1 : max 2 lo ≤ q) (h2 : q ≤ hi) : q ∈ GoldbachSieve.survivors lo hi c :=
  GoldbachSieve.mem_survivors.mpr
    ⟨h1, h2, fun r hrp _ hrd => (Nat.prime_dvd_prime_iff_eq hrp hq).mp hrd⟩
