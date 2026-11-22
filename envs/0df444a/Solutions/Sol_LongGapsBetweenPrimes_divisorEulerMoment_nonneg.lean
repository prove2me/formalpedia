-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:10.854069+00:00
-- url     : https://prove2.me/submissions/563e7245-d820-4e03-88f5-80d543f52d4c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P : ℕ) (γ : ℝ) : 0 ≤ divisorEulerMoment P γ :=
  Finset.sum_nonneg (fun _d _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _))
end LongGapsBetweenPrimes
