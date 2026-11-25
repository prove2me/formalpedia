-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:40.351264+00:00
-- url     : https://prove2.me/submissions/59c6ec59-5682-4128-af74-7d1026f92a15

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_Lp_two_norm_sq_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2 := by
  rw [SobolevSpace.norm_def, ← Lp.norm_fourier_eq, Lp_two_norm_sq_eq_integral]
  congr 1; ext ξ
  rw [← weight_smul_fourierFun, norm_smul, norm_weight, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num
end GroundTheory.Automorphic.Sobolev
