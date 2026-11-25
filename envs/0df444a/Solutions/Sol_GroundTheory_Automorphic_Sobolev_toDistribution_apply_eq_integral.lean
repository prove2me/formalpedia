-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.toDistribution_apply_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:16.344151+00:00
-- url     : https://prove2.me/submissions/4ac8766a-f673-496f-8a3f-3b4da302a5dc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integral_fourierInv_smul_eq_of_integrable
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral


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
theorem _root_.solution {s : ℝ} (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (u : SobolevSpace E F s) (φ : 𝓢(E, ℂ)) :
    SobolevSpace.toDistribution u φ = ∫ x, φ x • 𝓕⁻ (fourierFun u) x := by
  have h : 𝓕⁻ (𝓕 (SobolevSpace.toDistribution u)) = SobolevSpace.toDistribution u :=
    FourierTransform.fourierInv_fourier_eq _
  conv_lhs => rw [← h]
  rw [TemperedDistribution.fourierInv_apply, fourier_apply_eq_integral,
    SchwartzMap.fourierInv_coe, integral_fourierInv_smul_eq_of_integrable φ (integrable_fourierFun hs u)]
end GroundTheory.Automorphic.Sobolev
