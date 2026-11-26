-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampDerivativeLimitV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:31.807096+00:00
-- url     : https://prove2.me/submissions/384322a4-3a5e-4dc7-92b8-5311b6382ebb

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => min (1 : ℝ) (max 0 (x / ε n))) atTop
      (𝓝 (if 0 < x then 1 else 0)) := by
  by_cases hx : 0 < x
  · rw [if_pos hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim.eventually (eventually_lt_nhds hx)] with n hn
    have h : 1 ≤ x / ε n := (le_div_iff₀ (hε n)).2 (by simpa using hn.le)
    exact (min_eq_left (h.trans (le_max_right _ _))).symm
  · rw [if_neg hx]
    have h (n : ℕ) : min (1 : ℝ) (max 0 (x / ε n)) = 0 := by
      simp [max_eq_left (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) (hε n).le)]
    simpa only [h] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
