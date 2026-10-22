-- Prove2me | solution 1 for LNChannels.RateBounds.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:40:07.954842+00:00
-- url     : https://prove2.me/submissions/f33479a7-1eba-4c49-b87b-0e480f6b17da

import Mathlib
set_option autoImplicit false

theorem solution (B κ α : ℝ) (hB : 0 < B) (hκ : 0 < κ) (hα0 : 0 < α) (hα1 : α < 1)
    (hκα : α ^ 2 / (B * (1 - α)) ≤ κ) :
    α / κ ≤ 2 * B / (B * κ + √(B * κ * (B * κ + 4))) := by
  have ht : 0 < B * κ := mul_pos hB hκ
  have h1α : 0 < 1 - α := by linarith
  have ht3 : α ^ 2 ≤ B * κ * (1 - α) := by
    rw [div_le_iff₀ (mul_pos hB h1α)] at hκα
    nlinarith
  have hs : √(B * κ * (B * κ + 4)) ≤ (B * κ) * (2 - α) / α := by
    rw [Real.sqrt_le_iff]
    refine ⟨div_nonneg (mul_nonneg ht.le (by linarith)) hα0.le, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg ht.le (sub_nonneg.2 ht3)]
  have hs2 : √(B * κ * (B * κ + 4)) * α ≤ (B * κ) * (2 - α) := (le_div_iff₀ hα0).mp hs
  have hpos : 0 < B * κ + √(B * κ * (B * κ + 4)) := by positivity
  rw [div_le_div_iff₀ hκ hpos]
  nlinarith
