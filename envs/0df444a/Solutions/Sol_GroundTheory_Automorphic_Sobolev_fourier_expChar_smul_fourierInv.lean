-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_expChar_smul_fourierInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:11.908899+00:00
-- url     : https://prove2.me/submissions/7ba7d591-901e-47ff-a107-dddf05ac9e84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_expChar_eq_fourierChar

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (h : E) (φ : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ)) = SchwartzMap.compSubConstCLM ℂ (-h) φ := by
  apply SchwartzMap.ext; intro x
  rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, SchwartzMap.fourier_coe, Real.fourier_eq]
  have key : ∀ ξ : E, 𝐞 (-inner ℝ ξ x) • SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ) ξ =
      𝐞 (-inner ℝ ξ (x + h)) • (𝓕⁻ φ : 𝓢(E, ℂ)) ξ := by
    intro ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply (expChar_hasTemperateGrowth _), expChar_eq_fourierChar,
      Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_add_right, inner_neg_right]
    congr 3; ring
  simp_rw [key]
  rw [← Real.fourier_eq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
end GroundTheory.Automorphic.Sobolev
