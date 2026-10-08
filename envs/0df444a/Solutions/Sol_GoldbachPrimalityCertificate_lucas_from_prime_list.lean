-- Prove2me | solution 1 for GoldbachPrimalityCertificate.lucas_from_prime_list
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:57:08.954241+00:00
-- url     : https://prove2.me/submissions/dd0e944e-ec0c-4ac8-8db6-3ca130c4f54c

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false

namespace GoldbachPrimalityCertificate

private lemma prime_mem_of_dvd_prod (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (q : ℕ) (hq : Nat.Prime q)
    (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    simp only [List.prod_nil] at hd
    exact (hq.not_dvd_one hd).elim
  | cons r rs ih =>
    simp only [List.prod_cons] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have hr := hp r (by simp)
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
      simp [heq]
    · exact List.mem_cons_of_mem r (ih (fun s hs => hp s (List.mem_cons_of_mem r hs)) hd)

end GoldbachPrimalityCertificate

theorem solution (p : ℕ) (a : ZMod p) (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (hprod : factors.prod = p - 1)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ r ∈ factors, a ^ ((p - 1) / r) ≠ 1) : Nat.Prime p := by
  apply lucas_primality p a ha
  intro q hq hqd
  have hmem : q ∈ factors := GoldbachPrimalityCertificate.prime_mem_of_dvd_prod factors hp q hq
    (by rwa [hprod])
  exact hd q hmem

#print axioms solution
