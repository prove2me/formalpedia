-- Prove2me | solution 1 for LNChannels.RateBounds.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:14.828612+00:00
-- url     : https://prove2.me/submissions/a8645547-4d0c-457e-acdc-6ebe868daaf2

import Mathlib
set_option autoImplicit false

theorem solution (B κ C : ℝ) (hB : 0 < B) (hκ : 0 < κ) :
    let g : ℝ → ℝ := fun m => 2 * m + B * (2 / (κ ^ 2 * m ^ 2) - 1 / 6) - 2 * C / κ ^ 2
    let mhat := (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)
    0 < mhat ∧
      g mhat = 3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2 ∧
      ∀ m : ℝ, 0 < m → g mhat ≤ g m := by
  intro g mhat
  have hc : 0 < 2 * B / κ ^ 2 := by positivity
  have hm0 : 0 < mhat := Real.rpow_pos_of_pos hc _
  have hcube : mhat ^ 3 = 2 * B / κ ^ 2 := by
    show ((2 * B / κ ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = 2 * B / κ ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
  refine ⟨hm0, ?_, ?_⟩
  · have e : B = mhat ^ 3 * κ ^ 2 / 2 := by
      have := hcube
      field_simp at this
      linarith
    show 2 * mhat + B * (2 / (κ ^ 2 * mhat ^ 2) - 1 / 6) - 2 * C / κ ^ 2 =
      3 * mhat - B / 6 - 2 * C / κ ^ 2
    have hκ2 : κ ^ 2 ≠ 0 := by positivity
    have hm2 : mhat ≠ 0 := hm0.ne'
    rw [e]
    field_simp
    ring
  · intro m hm
    have e : B = mhat ^ 3 * κ ^ 2 / 2 := by
      have := hcube
      field_simp at this
      linarith
    have hκ2 : 0 < κ ^ 2 := by positivity
    show 2 * mhat + B * (2 / (κ ^ 2 * mhat ^ 2) - 1 / 6) - 2 * C / κ ^ 2 ≤
      2 * m + B * (2 / (κ ^ 2 * m ^ 2) - 1 / 6) - 2 * C / κ ^ 2
    rw [e]
    have key : 2 * m + mhat ^ 3 / m ^ 2 - 3 * mhat = (m - mhat) ^ 2 * (2 * m + mhat) / m ^ 2 := by
      field_simp
      ring
    have h1 : 0 ≤ (m - mhat) ^ 2 * (2 * m + mhat) / m ^ 2 := by positivity
    have h2 : 2 * mhat + mhat ^ 3 * κ ^ 2 / 2 * (2 / (κ ^ 2 * mhat ^ 2)) = 3 * mhat := by
      field_simp
      ring
    have h3 : 2 * m + mhat ^ 3 * κ ^ 2 / 2 * (2 / (κ ^ 2 * m ^ 2)) = 2 * m + mhat ^ 3 / m ^ 2 := by
      field_simp
    nlinarith [h1, key, h2, h3]
