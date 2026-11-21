-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:53:06.219214+00:00
-- url     : https://prove2.me/submissions/a73de071-a77b-4af4-92a9-206a0401bf81

import Mathlib
open scoped NNReal ENNReal Topology
theorem solution {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {w : E}
    (h : Filter.Tendsto (fun i => (‖u i - w‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 w) := by
  have hr : Filter.Tendsto (fun i => ‖u i - w‖ ^ 2) Filter.atTop (𝓝 0) := by
    have hc : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
      ENNReal.continuousAt_toReal (by simp)
    simpa [Function.comp_def, ENNReal.toReal_pow] using hc.tendsto.comp h
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hn : Filter.Tendsto (fun i => ‖u i - w‖) Filter.atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hn
