-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:26.34783+00:00
-- url     : https://prove2.me/submissions/99b57a18-c9c8-4a97-ab95-e680e5739985

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) (ξ : E) :
    (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) * ∫⁻ η, K (ξ - η) * G η ^ 2 := by
  have hK' : Measurable fun η : E ↦ K (ξ - η) := hK.comp (measurable_const.sub measurable_id)
  have h := L2Kernel.lintegral_mul_sq_le (volume : Measure E)
    (f := fun η ↦ K (ξ - η) ^ (1 / 2 : ℝ)) (g := fun η ↦ K (ξ - η) ^ (1 / 2 : ℝ) * G η)
    (hK'.pow_const _).aemeasurable ((hK'.pow_const _).mul hG).aemeasurable
  have e2 : ∀ η, (K (ξ - η) ^ (1 / 2 : ℝ)) ^ 2 = K (ξ - η) := by
    intro η; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have e1 : ∀ η, K (ξ - η) ^ (1 / 2 : ℝ) * (K (ξ - η) ^ (1 / 2 : ℝ) * G η) = K (ξ - η) * G η := by
    intro η; rw [← mul_assoc, ← pow_two, e2]
  have e3 : ∀ η, (K (ξ - η) ^ (1 / 2 : ℝ) * G η) ^ 2 = K (ξ - η) * G η ^ 2 := by
    intro η; rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  rwa [lintegral_sub_left_eq_self K ξ] at h
end GroundTheory.Automorphic.Sobolev
