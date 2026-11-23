-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagNNRealUniformLimitRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:07:41.507959+00:00
-- url     : https://prove2.me/submissions/fb15bf0a-bd22-4fb0-ac2e-15a241c2e90d

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ)
    (happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - f t| < δ) :
    ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t := by
  intro t
  let T : ℝ≥0 := t + 1
  have htT : t < T := by
    dsimp [T]
    linarith
  obtain ⟨F, hF, huni⟩ := happrox T (lt_of_le_of_lt bot_le htT)
  have hstayR : ∀ᶠ s in 𝓝[≥] t, s ≤ T := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htT)] with s hs
    exact hs.le
  change Tendsto f (𝓝[≥] t) (𝓝 (f t))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := huni (ε / 3) (by positivity)
  have hnear : ∀ᶠ s in 𝓝[≥] t, dist (F n s) (F n t) < ε / 3 :=
    ((hF n t).1).eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hstayR, hnear] with s hsT hsnear
  have hfs : dist (f s) (F n s) < ε / 3 := by
    rw [dist_comm]
    simpa only [Real.dist_eq] using hn n le_rfl s hsT
  have hft : dist (F n t) (f t) < ε / 3 := by
    simpa only [Real.dist_eq] using hn n le_rfl t htT.le
  have htri : dist (f s) (f t) ≤
      dist (f s) (F n s) + dist (F n s) (F n t) +
      dist (F n t) (f t) := dist_triangle4 _ _ _ _
  linarith
