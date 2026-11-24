-- Prove2me | solution 1 for GlobalTheory.RapidFourier.norm_wave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:47.764545+00:00
-- url     : https://prove2.me/submissions/2fb2c115-7b4c-4c12-a25b-578814312a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution (a : ℂ) (t : ℝ) : ‖wave a t‖ = ‖a‖ := by
  have h : (2 * π * I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [wave, norm_mul, h, Complex.norm_exp_ofReal_mul_I, mul_one]
end GlobalTheory.RapidFourier
