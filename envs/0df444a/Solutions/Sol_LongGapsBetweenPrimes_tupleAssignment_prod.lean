-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleAssignment_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:59.376811+00:00
-- url     : https://prove2.me/submissions/3c3a7037-8b37-4fdc-a458-45ef3482a91e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_eq_some

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} {M : Type*} [CommMonoid M]
    (r : DivisorTuple P k) (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (f : PrimeIndex P → Fin k → M) :
    (∏ p : PrimeIndex P, match tupleAssignment r p with | none => 1 | some i => f p i) =
      ∏ i, ∏ p : PrimeIndex P, if p.val ∣ (r i).val then f p i else 1 := by
  classical
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  simp_rw [← tupleAssignment_eq_some r hpair p]
  cases tupleAssignment r p <;> simp
end LongGapsBetweenPrimes
