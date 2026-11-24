-- Prove2me | solution 1 for GlobalTheory.RapidFourier.norm_two_pi_I
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:47.434525+00:00
-- url     : https://prove2.me/submissions/1776dd6e-a0e9-4608-a5b9-d4d5d1ac12fd

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
theorem _root_.solution : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_one]
  norm_num
end GlobalTheory.RapidFourier
