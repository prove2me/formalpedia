-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.convolution_reflect_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:33.326902+00:00
-- url     : https://prove2.me/submissions/176e821a-0cb4-4f11-9730-22131b7f1cf0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_reflect
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (ψ φ : 𝓢(E, ℂ)) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ =
      𝓕 (SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) := by
  apply SchwartzMap.ext; intro x
  have hψ := (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth
  simp only [SchwartzMap.convolution, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, fourierInvCLM_apply, fourierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_comp_neg]
  have h : (fun y ↦ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (reflect E ψ)) (𝓕 φ))
      (-y)) = (⇑(SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) : E → ℂ) := by
    funext y
    rw [SchwartzMap.pairing_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hψ, fourier_reflect,
      neg_neg, ContinuousLinearMap.mul_apply', smul_eq_mul, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
    rfl
  exact congrArg (fun g : E → ℂ ↦ 𝓕 g x) h
end GroundTheory.Automorphic.Sobolev
