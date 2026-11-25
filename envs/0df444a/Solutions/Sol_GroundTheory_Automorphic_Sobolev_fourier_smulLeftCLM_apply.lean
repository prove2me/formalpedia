-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_smulLeftCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:21:09.527311+00:00
-- url     : https://prove2.me/submissions/8cce8876-83e9-4651-9dfe-fdf4c4091481

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_char_smul
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
theorem _root_.solution (χ φ : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) : 𝓢(E, ℂ)) ξ =
      ∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 φ : 𝓢(E, ℂ)) η := by
  have hφ : ∀ x, φ x = ∫ η, (𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η := by
    intro x
    have h0 : (𝓕⁻ (𝓕 φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) = φ := FourierTransform.fourierInv_fourier_eq φ
    have h : (𝓕⁻ (𝓕 φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) x = φ x := by rw [h0]
    rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    rfl
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  have hint : Integrable (Function.uncurry fun x η : E ↦
      (𝐞 (-inner ℝ x ξ) : ℂ) * χ x * ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η))
      ((volume : Measure E).prod volume) := by
    have h := (χ.integrable (μ := (volume : Measure E))).mul_prod
      ((𝓕 φ : 𝓢(E, ℂ)).integrable (μ := (volume : Measure E)))
    refine h.norm.mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact Continuous.aestronglyMeasurable (by
        have h1 := χ.continuous
        have h2 := (𝓕 φ : 𝓢(E, ℂ)).continuous
        fun_prop)
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl
  calc ∫ x, 𝐞 (-inner ℝ x ξ) • (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) x
      = ∫ x, ∫ η, (𝐞 (-inner ℝ x ξ) : ℂ) * χ x *
          ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η) := by
        congr 1; ext x
        rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hφ x, Circle.smul_def,
          smul_eq_mul, smul_eq_mul]
        simp_rw [← integral_const_mul]
        congr 1; ext η; ring
    _ = ∫ η, ∫ x, (𝐞 (-inner ℝ x ξ) : ℂ) * χ x *
          ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η) := integral_integral_swap hint
    _ = _ := by
        congr 1; ext η
        rw [← fourier_char_smul χ η ξ, Real.fourier_eq, ← integral_mul_const]
        congr 1; ext x
        rw [Circle.smul_def, smul_eq_mul, real_inner_comm η x]
        ring
end GroundTheory.Automorphic.Sobolev
