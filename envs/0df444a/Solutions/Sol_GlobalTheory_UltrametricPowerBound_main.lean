-- Prove2me | solution 1 for GlobalTheory.UltrametricPowerBound.main
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:16:58.307798+00:00
-- url     : https://prove2.me/submissions/f8ae242d-60d2-4191-aaed-5d98508405ad

import Mathlib


theorem solution : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  have lin (n : ℕ) : ‖w^n - 1‖ ≤ ‖w-1‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show w^(n+1)-1 = (w^n-1)*w + (w-1) by ring]
      apply (IsUltrametricDist.norm_add_le_max _ _).trans; apply max_le _ le_rfl
      rw [norm_mul]; simpa using mul_le_mul ih hw (norm_nonneg _) (norm_nonneg _)
  induction k with
  | zero => simp [sq_nonneg]
  | succ k ih =>
    rw [show w^(k+1)-1-((k+1:ℕ):ℚ_[l])*(w-1) = (w^k-1-(k:ℚ_[l])*(w-1)) + (w^k-1)*(w-1) by push_cast; ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans; apply max_le ih
    rw [norm_mul, pow_two]; exact mul_le_mul_of_nonneg_right (lin k) (norm_nonneg _)
