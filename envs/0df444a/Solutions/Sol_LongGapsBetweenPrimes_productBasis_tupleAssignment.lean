-- Prove2me | solution 1 for LongGapsBetweenPrimes.productBasis_tupleAssignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:24.701514+00:00
-- url     : https://prove2.me/submissions/988ce5e6-b10c-413d-9c8b-59caaf56ddac

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_prod

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (r : DivisorTuple P k)
    (hr : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (t : (p : PrimeIndex P) → Fin p.val) :
    productBasis f (tupleAssignment r) t = ∏ i, coordinateBasis f (r i) i t := by
  classical
  unfold productBasis coordinateBasis
  rw [← tupleAssignment_prod r hr]
  apply Finset.prod_congr rfl
  intro p _
  cases tupleAssignment r p <;> simp [hf]
end LongGapsBetweenPrimes
