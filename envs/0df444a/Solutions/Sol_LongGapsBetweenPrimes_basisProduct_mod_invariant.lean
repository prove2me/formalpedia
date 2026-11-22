-- Prove2me | solution 1 for LongGapsBetweenPrimes.basisProduct_mod_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:32.658629+00:00
-- url     : https://prove2.me/submissions/6f46d712-7287-4221-978b-1aa38e131d84

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_assignmentProduct

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (σ : PrimeIndex P → Option (Fin k)) (n : ℕ) :
    productBasis f σ (residueVector P (n % assignmentProduct (fun p : PrimeIndex P => p.val) σ)) =
      productBasis f σ (residueVector P n) := by
  unfold productBasis
  apply Finset.prod_congr rfl
  intro p _
  cases hσ : σ p with
  | none => simp only [hf]
  | some i =>
      congr 1
      exact Fin.ext (Nat.mod_mod_of_dvd n
        (prime_dvd_assignmentProduct σ p (by simp [hσ])))
end LongGapsBetweenPrimes
