-- Prove2me | solution 1 for LongGapsBetweenPrimes.diagonal_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:21.262806+00:00
-- url     : https://prove2.me/submissions/42178be2-ae50-4579-8029-f4db7dbf159a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_moment_tail_le
import Theorems.Thm_LongGapsBetweenPrimes_tupleMass_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_sum_tupleMass_mul_rpow

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P k : ℕ) {D β : ℝ} (hD : 0 < D) (hβ : 0 ≤ β) :
    (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
        (fun r => D < (tupleProduct r : ℝ)), tupleMass r) ≤
      D ^ (-β) * coefficientMoment P β ^ k := by
  classical
  simpa only [sum_tupleMass_mul_rpow] using
    moment_tail_le Finset.univ tupleMass (fun r : DivisorTuple P k => (tupleProduct r : ℝ))
      D β hD hβ (fun r _ => tupleMass_nonneg r) (fun r _ => Nat.cast_nonneg _)
end LongGapsBetweenPrimes
