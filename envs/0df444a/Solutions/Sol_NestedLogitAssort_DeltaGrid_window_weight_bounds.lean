-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.window_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:56:54.647176+00:00
-- url     : https://prove2.me/submissions/197a280f-ce2d-4651-b0cf-de3b7a1605f6

import Mathlib

theorem solution (δ : ℝ) (hδ : 1 < δ) (γ : ℝ) (hγ : 0 ≤ γ) (l : ℤ) (W : ℝ)
    (hW1 : δ ^ (l - 1) ≤ W) (hW2 : W ≤ δ ^ l) :
    δ ^ (-(max (1 - γ) 0)) * W ^ (γ - 1) ≤ (δ ^ l) ^ (γ - 1) ∧
      (δ ^ (l - 1)) ^ γ ≤ W ^ γ := by
  have hδ0 : 0 < δ := by linarith
  have hWpos : 0 < W := lt_of_lt_of_le (zpow_pos hδ0 _) hW1
  have hdl : 0 < δ ^ l := zpow_pos hδ0 l
  refine ⟨?_, Real.rpow_le_rpow (zpow_pos hδ0 _).le hW1 hγ⟩
  rcases le_or_gt 1 γ with h1 | h1
  · rw [max_eq_right (by linarith : 1 - γ ≤ 0), neg_zero, Real.rpow_zero, one_mul]
    exact Real.rpow_le_rpow hWpos.le hW2 (by linarith)
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - γ), neg_sub,
      ← Real.mul_rpow hδ0.le hWpos.le]
    have hle : δ ^ l ≤ δ * W := by
      have h := mul_le_mul_of_nonneg_left hW1 hδ0.le
      rw [zpow_sub_one₀ hδ0.ne'] at h
      calc δ ^ l = δ * (δ ^ l * δ⁻¹) := by
            rw [mul_comm (δ ^ l) δ⁻¹, mul_inv_cancel_left₀ hδ0.ne']
        _ ≤ δ * W := h
    exact Real.rpow_le_rpow_of_nonpos hdl hle (by linarith)
