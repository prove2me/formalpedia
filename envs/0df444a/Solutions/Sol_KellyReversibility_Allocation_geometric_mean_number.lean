-- Prove2me | solution 1 for KellyReversibility.Allocation.geometric_mean_number
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:50:58.854715+00:00
-- url     : https://prove2.me/submissions/cc96792a-53fe-48be-86ba-0c35c84e6237

import Mathlib

theorem solution (a φ : ℝ) (ha : 0 < a) (haφ : a < φ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((1 - a / φ) * (a / φ) ^ n)) (a / (φ - a)) := by
  have hφ : 0 < φ := ha.trans haφ
  have hr0 : 0 ≤ a / φ := div_nonneg ha.le hφ.le
  have hr1 : a / φ < 1 := (div_lt_one hφ).2 haφ
  have hn : ‖a / φ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 - a / φ)
  have hne : φ - a ≠ 0 := by linarith
  have hφne : φ ≠ 0 := hφ.ne'
  have hf : (fun n : ℕ => (n : ℝ) * ((1 - a / φ) * (a / φ) ^ n))
      = fun i : ℕ => (1 - a / φ) * ((i : ℝ) * (a / φ) ^ i) := by
    funext n; ring
  have h1 : 1 - a / φ = (φ - a) / φ := by field_simp
  have hv : a / (φ - a) = (1 - a / φ) * (a / φ / (1 - a / φ) ^ 2) := by
    rw [h1]
    field_simp
  rw [hf, hv]
  exact h
