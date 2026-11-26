-- Prove2me | solution 1 for Kyprianou.Ch04.leftLimitsFromCompactUniformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:15.957672+00:00
-- url     : https://prove2.me/submissions/865ef9b3-30b8-4979-9213-431ad284e0c2

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Compact uniform convergence passes to positive-time left limits. -/
theorem solution (U L : ℕ → NNReal → ℝ) (X Y : NNReal → ℝ)
    (hU : ∀ n t, 0 < t → Tendsto (U n) (𝓝[<] t) (𝓝 (L n t)))
    (hX : ∀ t, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (Y t)))
    (h : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |U n t - X t| < δ) :
    ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, 0 < t → t ≤ T → |L n t - Y t| < δ := by
  intro T δ hδ
  obtain ⟨N,hN⟩ := h T (δ/2) (by linarith)
  refine ⟨N,fun n hn t ht htT => ?_⟩
  haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  have hh : |L n t - Y t| ≤ δ/2 := by
    apply le_of_tendsto ((hU n t ht).sub (hX t ht)).abs
    filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
    exact (hN n hn s (hs.le.trans htT)).le
  linarith
