-- Prove2me | solution 1 for KellerTrotter2017.thm7_14_totient_product_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:57:49.441068+00:00
-- url     : https://prove2.me/submissions/1af86a17-211d-4afe-949c-80e94dbef7ac

import Mathlib

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (Nat.totient n : ℚ) = n * ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / p) := by
  rw [Nat.totient_eq_mul_prod_factors]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have : (p : ℚ) ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).pos; positivity
  field_simp
