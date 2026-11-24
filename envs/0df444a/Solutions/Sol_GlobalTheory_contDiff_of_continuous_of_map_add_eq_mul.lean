-- Prove2me | solution 1 for GlobalTheory.contDiff_of_continuous_of_map_add_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:54.061313+00:00
-- url     : https://prove2.me/submissions/4abebd45-79d1-4455-8613-5fbfedc8c70c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
open MeasureTheory Filter Topology
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℂ) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : ContDiff ℝ ∞ f := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hb hf 0
  obtain ⟨n, hn⟩ := (ht.eventually_ne h0).exists
  have hs : ContDiff ℝ ∞
      (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :=
    HasCompactSupport.contDiff_convolution_left _ (b n).hasCompactSupport_normed
      (b n).contDiff_normed hf.locallyIntegrable
  have key : ∀ x, convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      = f x * convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0 := by
    intro x
    rw [convolution_def, convolution_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : x - t = x + (0 - t) := by abel
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [this, hadd, mul_smul_comm]
  have : f = fun x => convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      * (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0)⁻¹ := by
    funext x
    rw [key x, mul_inv_cancel_right₀ hn]
  rw [this]
  exact hs.mul contDiff_const
end GlobalTheory
