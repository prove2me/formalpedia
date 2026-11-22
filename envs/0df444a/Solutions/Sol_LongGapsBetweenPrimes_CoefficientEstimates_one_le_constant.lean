-- Prove2me | solution 1 for LongGapsBetweenPrimes.CoefficientEstimates.one_le_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:20.976092+00:00
-- url     : https://prove2.me/submissions/f6ba3d60-e832-4a24-92b2-6d46f60a7e6b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientAbsMoment_zero

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
namespace CoefficientEstimates
theorem _root_.solution {P : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) : 1 ≤ C := by
  simpa [coefficientAbsMoment_zero h.one_lt] using h.absMoment_le 0 le_rfl (by positivity)
end CoefficientEstimates
end LongGapsBetweenPrimes
