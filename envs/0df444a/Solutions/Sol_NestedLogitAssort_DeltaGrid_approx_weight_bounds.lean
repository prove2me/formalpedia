-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.approx_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:52:27.680538+00:00
-- url     : https://prove2.me/submissions/dffbf273-b0c9-4fee-bd36-b1c4ddb6b695

import Mathlib

theorem solution (δ : ℝ) (hδ : 1 < δ) (γ : ℝ) (hγ : 0 ≤ γ) (l : ℤ) (W : ℝ)
    (hW1 : δ ^ (l - 1) ≤ W) (hW2 : W ≤ δ ^ l) :
    (δ ^ l) ^ (γ - 1) * δ ^ (-(max (γ - 1) 0)) ≤ W ^ (γ - 1) ∧
      W ^ γ ≤ (δ ^ l) ^ γ := by
  have hδ0 : 0 < δ := by linarith
  have hWpos : 0 < W := lt_of_lt_of_le (zpow_pos hδ0 _) hW1
  have hdl : 0 < δ ^ l := zpow_pos hδ0 l
  refine ⟨?_, Real.rpow_le_rpow hWpos.le hW2 hγ⟩
  rcases le_or_gt 1 γ with h1 | h1
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ γ - 1), Real.rpow_neg hδ0.le, ← div_eq_mul_inv,
      ← Real.div_rpow hdl.le hδ0.le, div_eq_mul_inv, ← zpow_sub_one₀ hδ0.ne']
    exact Real.rpow_le_rpow (zpow_pos hδ0 _).le hW1 (by linarith)
  · rw [max_eq_right (by linarith : γ - 1 ≤ 0), neg_zero, Real.rpow_zero, mul_one]
    exact Real.rpow_le_rpow_of_nonpos hWpos hW2 (by linarith)
