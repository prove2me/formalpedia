-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memLp_two_weight_mul_norm_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:25.178972+00:00
-- url     : https://prove2.me/submissions/bbfed466-2d5c-40ee-b268-ec0957206e29

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    MemLp (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖fourierFun u ξ‖) 2 (volume : Measure E) := by
  have h := Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))
  refine h.norm.congr_norm ?_ ?_
  · have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
    exact hc.aestronglyMeasurable.mul (fourierFun_aestronglyMeasurable u).norm
  · refine ae_of_all _ fun ξ ↦ ?_
    rw [← weight_smul_fourierFun, norm_norm, norm_smul, norm_weight, norm_mul, norm_norm,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
end GroundTheory.Automorphic.Sobolev
