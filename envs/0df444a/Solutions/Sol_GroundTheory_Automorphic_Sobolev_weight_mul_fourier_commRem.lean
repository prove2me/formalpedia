-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.weight_mul_fourier_commRem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:26.492539+00:00
-- url     : https://prove2.me/submissions/91a39a4e-e0fd-495a-9270-999bec3315d8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_smulLeftCLM_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_weight_apply
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
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    weight r ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ =
      ∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * ((weight r ξ - weight r η) * (𝓕 φ : 𝓢(E, ℂ)) η) := by
  have hw : weight r ξ * weight (-r) ξ = 1 := by
    rw [weight_mul_weight, add_neg_cancel]; simp [weight]
  have hi1 : Integrable (fun η ↦ (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 φ : 𝓢(E, ℂ)) η) volume := by
    refine ((𝓕 φ : 𝓢(E, ℂ)).integrable (μ := (volume : Measure E))).bdd_mul
      (c := SchwartzMap.seminorm ℝ 0 0 (𝓕 χ : 𝓢(E, ℂ))) ?_ ?_
    · exact ((𝓕 χ : 𝓢(E, ℂ)).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ fun η ↦ SchwartzMap.norm_le_seminorm ℝ _ _
  have hi2 : Integrable (fun η ↦ (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) *
      (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) η) volume := by
    refine ((𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)).integrable
      (μ := (volume : Measure E))).bdd_mul
      (c := SchwartzMap.seminorm ℝ 0 0 (𝓕 χ : 𝓢(E, ℂ))) ?_ ?_
    · exact ((𝓕 χ : 𝓢(E, ℂ)).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ fun η ↦ SchwartzMap.norm_le_seminorm ℝ _ _
  have e : (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) = 𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) -
      𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight (-r))
        (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ))) := by
    simp only [commRem, sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg]
  rw [e, sub_apply, fourier_fourierMultiplierCLM_weight_apply, fourier_smulLeftCLM_apply,
    fourier_smulLeftCLM_apply]
  rw [mul_sub, ← mul_assoc, hw, one_mul, ← integral_const_mul, ← integral_sub (hi1.const_mul _) hi2]
  congr 1; ext η
  rw [fourier_fourierMultiplierCLM_weight_apply]
  ring
end GroundTheory.Automorphic.Sobolev
