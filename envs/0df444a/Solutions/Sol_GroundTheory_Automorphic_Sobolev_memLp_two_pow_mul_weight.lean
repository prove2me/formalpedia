-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memLp_two_pow_mul_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:24.397851+00:00
-- url     : https://prove2.me/submissions/35fa136a-ea94-41c3-b606-1fc5aaef3670

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding

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
theorem _root_.solution {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) :
    MemLp (fun ξ : E ↦ ‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 (volume : Measure E) := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E)) hj
  have hmeas : AEStronglyMeasurable (fun ξ : E ↦ ‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2))
      (volume : Measure E) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_norm.pow j).mul
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne')
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.mono' (hmeas.norm.pow 2) (ae_of_all _ fun ξ ↦ ?_)
  have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2
      = (‖ξ‖ ^ 2) ^ j * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 := by ring
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ j * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 := by
        gcongr; linarith
    _ = (1 + ‖ξ‖ ^ 2) ^ (-(2 * (s - j)) / 2) := by
        have e1 : ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; congr 1; push_cast; ring
        have e2 : (1 + ‖ξ‖ ^ 2) ^ j = (1 + ‖ξ‖ ^ 2) ^ (j : ℝ) := (Real.rpow_natCast _ _).symm
        rw [e1, e2, ← Real.rpow_add h0]; congr 1; ring
end GroundTheory.Automorphic.Sobolev
