-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.rpow_eq_sqrt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:14.769128+00:00
-- url     : https://prove2.me/submissions/4c7879c5-7796-438d-94bc-263fd7810fc0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (ξ : E) (k : ℕ) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) = Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) k,
    ← Real.rpow_mul (by positivity)]
  congr 1; ring
end GroundTheory.Automorphic.Sobolev
