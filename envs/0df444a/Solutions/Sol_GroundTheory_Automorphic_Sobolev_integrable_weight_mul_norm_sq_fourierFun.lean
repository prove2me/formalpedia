-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integrable_weight_mul_norm_sq_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:40.042731+00:00
-- url     : https://prove2.me/submissions/1224cbce-9010-475d-acf4-992dfa6f9a6d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



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
theorem _root_.solution (u : SobolevSpace E F s) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2) (volume : Measure E) := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1
    (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)))
  refine h.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [← weight_smul_fourierFun, norm_smul, norm_weight, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num
end GroundTheory.Automorphic.Sobolev
