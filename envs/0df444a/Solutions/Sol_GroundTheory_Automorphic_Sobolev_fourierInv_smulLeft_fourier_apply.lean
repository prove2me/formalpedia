-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourierInv_smulLeft_fourier_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:48:37.141534+00:00
-- url     : https://prove2.me/submissions/9ad978bd-60a0-4135-83de-e7c31fa3b37c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_char_smul
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integral_fourier_smul_eq_of_integrable
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ φ : 𝓢(E, ℂ)) (η : E) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ)) : 𝓢(E, ℂ)) η =
      ∫ ξ, φ ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  have hg : Integrable (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) (volume : Measure E) := by
    refine (χ.integrable (μ := (volume : Measure E))).bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact ae_of_all _ fun x ↦ (Circle.norm_coe _).le
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  have h := integral_fourier_smul_eq_of_integrable (F := ℂ) φ hg
  simp only [smul_eq_mul] at h
  simp_rw [fourier_char_smul] at h
  rw [← h]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, Circle.smul_def, smul_eq_mul,
    smul_eq_mul, SchwartzMap.fourier_coe]
  ring
end GroundTheory.Automorphic.Sobolev
