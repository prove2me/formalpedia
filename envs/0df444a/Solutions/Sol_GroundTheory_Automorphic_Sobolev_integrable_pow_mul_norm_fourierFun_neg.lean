-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integrable_pow_mul_norm_fourierFun_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:52.058234+00:00
-- url     : https://prove2.me/submissions/916e14ea-524b-4e27-99f0-6d05bf9e4f01

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_pow_mul_norm_fourierFun
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
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ j * ‖fourierFun u (-ξ)‖) (volume : Measure E) := by
  have h := (integrable_pow_mul_norm_fourierFun hj u).comp_neg
  simpa [Function.comp_def, norm_neg] using h
end GroundTheory.Automorphic.Sobolev
