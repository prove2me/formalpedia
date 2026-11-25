-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_apply_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:08.445737+00:00
-- url     : https://prove2.me/submissions/48904582-72a2-4674-9ba4-973cb95c9f3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_weight_fourier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integral_smul_weight

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
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) (φ : 𝓢(E, ℂ)) :
    𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • fourierFun u ξ := by
  have h1 : 𝓕 (SobolevSpace.toDistribution u) =
      smulLeftCLM F (weight (-s)) (smulLeftCLM F (weight s) (𝓕 (SobolevSpace.toDistribution u))) := by
    rw [smulLeftCLM_smulLeftCLM_apply (weight_hasTemperateGrowth _) (weight_hasTemperateGrowth _)]
    have : (weight s * weight (-s) : E → ℂ) = fun _ ↦ 1 := by
      funext ξ; simp only [Pi.mul_apply]; rw [weight_mul_weight]; simp [weight]
    rw [this, smulLeftCLM_const, one_smul]
  rw [h1, smulLeftCLM_weight_fourier, smulLeftCLM_apply_apply, integral_smul_weight]
  rfl
end GroundTheory.Automorphic.Sobolev
