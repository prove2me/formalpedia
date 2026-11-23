-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagNNRealUniformLimitLeftLimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:10:20.087621+00:00
-- url     : https://prove2.me/submissions/2c598f12-b412-434c-90a4-92bf11dc9140

import Theorems.Thm_Kyprianou_Ch02_cadlagUniformApproxLeftLimCauchyV1
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
    ∀ t : ℝ≥0, ∃ l : ℝ,
      Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l) := by
  intro t
  let T : ℝ≥0 := t + 1
  have htT : t < T := by
    dsimp [T]
    linarith
  obtain ⟨F, hF, huni⟩ := happrox T (lt_of_le_of_lt bot_le htT)
  by_cases ht : 0 < t
  · choose l hl using fun n => (hF n t).2
    haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    have hstayL : ∀ᶠ s in 𝓝[<] t, s ≤ T := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hs.le.trans htT.le
    have hcauchy : CauchySeq l :=
      Kyprianou.Ch02.cadlagUniformApproxLeftLimCauchyV1
        f t ht F l hl (by simpa only [T] using huni)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨L, ?_⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := huni (ε / 3) (by positivity)
    have hLev : ∀ᶠ n in atTop, dist (l n) L < ε / 3 :=
      Metric.tendsto_nhds.mp hL (ε / 3) (by positivity)
    have hUev : ∀ᶠ n in atTop,
        ∀ s : ℝ≥0, s ≤ T → |F n s - f s| < ε / 3 :=
      eventually_atTop.mpr ⟨N, fun n hn => hN n hn⟩
    obtain ⟨n, hUn, hnL⟩ := (hUev.and hLev).exists
    have hnear : ∀ᶠ s in 𝓝[<] t, dist (F n s) (l n) < ε / 3 :=
      (hl n).eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [hnear, hstayL] with s hsnear hsT
    have hfs : dist (f s) (F n s) < ε / 3 := by
      rw [dist_comm]
      simpa only [Real.dist_eq] using hUn s hsT
    have htri : dist (f s) L ≤
        dist (f s) (F n s) + dist (F n s) (l n) +
        dist (l n) L := dist_triangle4 _ _ _ _
    linarith
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) bot_le
    subst t
    exact ⟨0, by simp [Set.Iio_bot, nhdsWithin_empty]⟩
