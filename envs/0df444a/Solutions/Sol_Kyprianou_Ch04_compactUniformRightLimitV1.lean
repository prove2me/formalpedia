-- Prove2me | solution 1 for Kyprianou.Ch04.compactUniformRightLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:53:11.850856+00:00
-- url     : https://prove2.me/submissions/e4e30586-4726-472d-a2e4-c7cdfae49c6c

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Compact uniform limits of right-continuous paths are right-continuous. -/
theorem solution (Y : ℕ → NNReal → ℝ) (M : NNReal → ℝ)
    (hY : ∀ n t, Tendsto (Y n) (𝓝[>] t) (𝓝 (Y n t)))
    (hM : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |Y n t - M t| < δ) :
    ∀ t, Tendsto M (𝓝[>] t) (𝓝 (M t)) := by
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := hM (t+1) (ε/3) (by positivity)
  have h := Metric.tendsto_nhds.mp (hY N t) (ε/3) (by positivity)
  have ht : ∀ᶠ s in 𝓝[>] t, s < t+1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by simp))
  filter_upwards [h,ht] with s hs hst
  rw [Real.dist_eq] at hs ⊢
  have ha := hN N le_rfl s hst.le
  have hb := hN N le_rfl t (by simp)
  have hc : |M s - M t| ≤ |M s - Y N s| + |Y N s - Y N t| + |Y N t - M t| := by
    calc
      _ = |(M s - Y N s) + (Y N s - Y N t) + (Y N t - M t)| := by ring_nf
      _ ≤ |(M s - Y N s) + (Y N s - Y N t)| + |Y N t - M t| := abs_add_le ((M s - Y N s) + (Y N s - Y N t)) (Y N t - M t)
      _ ≤ _ := add_le_add_left (abs_add_le (M s - Y N s) (Y N s - Y N t)) _
  rw [abs_sub_comm (M s) (Y N s)] at hc
  linarith
