-- Prove2me | solution 1 for Gilbreath.prime_gap_positive_normalization
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-25T14:11:14.295838+00:00
-- url     : https://prove2.me/submissions/ed5b371e-bb90-44c2-87b0-cd3fc8ba94e5

import Definitions.Def_gilbreath_triangle

set_option autoImplicit false
open Gilbreath

private theorem prime_tail_odd (n : ℕ) : Odd (Nat.nth Nat.Prime (n + 1)) := by
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1)
  apply hp.odd_of_ne_two
  have hlt := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 0 < n + 1 by omega)
  simpa using ne_of_gt hlt

private theorem prime_gap_tail_even (n : ℕ) : Even (d 1 (n + 1)) := by
  change Even (Int.natAbs
    ((Nat.nth Nat.Prime ((n + 1) + 1) : ℤ) -
      (Nat.nth Nat.Prime (n + 1) : ℤ)))
  have hnext : Odd (Nat.nth Nat.Prime ((n + 1) + 1) : ℤ) := by
    exact_mod_cast prime_tail_odd (n + 1)
  have hprev : Odd (Nat.nth Nat.Prime (n + 1) : ℤ) := by
    exact_mod_cast prime_tail_odd n
  exact (hnext.sub_odd hprev).natAbs

theorem solution :
    ∃! b : ℕ → ℕ, (∀ n, d 1 (n + 1) = 2 * b n) ∧ (∀ n, 1 ≤ b n) := by
  let b : ℕ → ℕ := fun n => d 1 (n + 1) / 2
  have hb (n : ℕ) : d 1 (n + 1) = 2 * b n := by
    obtain ⟨j, hj⟩ := prime_gap_tail_even n
    change d 1 (n + 1) = 2 * (d 1 (n + 1) / 2)
    omega
  have hpos (n : ℕ) : 1 ≤ b n := by
    have hlt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
      (show n + 1 < (n + 1) + 1 by omega)
    have hint : (Nat.nth Nat.Prime (n + 1) : ℤ) <
        (Nat.nth Nat.Prime ((n + 1) + 1) : ℤ) := by exact_mod_cast hlt
    have hdiff : d 1 (n + 1) ≠ 0 := by
      change Int.natAbs
        ((Nat.nth Nat.Prime ((n + 1) + 1) : ℤ) -
          (Nat.nth Nat.Prime (n + 1) : ℤ)) ≠ 0
      intro hz
      have hzero := Int.natAbs_eq_zero.mp hz
      omega
    have h := hb n
    omega
  refine ⟨b, ⟨hb, hpos⟩, ?_⟩
  intro y hy
  funext n
  have h₁ := hb n
  have h₂ := hy.1 n
  omega

#print axioms solution
