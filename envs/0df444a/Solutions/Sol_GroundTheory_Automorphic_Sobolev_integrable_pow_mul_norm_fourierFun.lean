-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integrable_pow_mul_norm_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:39.003989+00:00
-- url     : https://prove2.me/submissions/88949cda-55c5-4fd4-95f6-c2cf42b5203d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_pow_mul_weight
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_weight_mul_norm_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) (u : SobolevSpace E F s) :
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ j * ‖fourierFun u ξ‖) (volume : Measure E) := by
  have h := (memLp_two_pow_mul_weight (s := s) hj).integrable_mul
    (memLp_two_weight_mul_norm_fourierFun u)
  refine h.congr (ae_of_all _ fun ξ ↦ ?_)
  have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← mul_assoc ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)), ← Real.rpow_add h0,
    show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero, one_mul]
end GroundTheory.Automorphic.Sobolev
