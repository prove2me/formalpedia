-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:13.295793+00:00
-- url     : https://prove2.me/submissions/0b56aa9c-82c1-4f95-b1ee-9f041db6e5f4

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : P ≠ 0) (d : DivisorIndex P) :
    0 ≤ divisorProbability P d := by
  exact div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (zero_le_one.trans (coefficientMoment_ge_one hP 0))
end LongGapsBetweenPrimes
