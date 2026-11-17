-- Prove2me | solution 1 for LightningNetwork.RateBounds.eq_24_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:54:43.65424+00:00
-- url     : https://prove2.me/submissions/dbe2d28b-00f8-496b-be78-2f3ac2cab0ce

import Mathlib

theorem solution (B C κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) :
    0 ≤ 3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2 ↔
      C ≤ 3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 := by
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hcube : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 3]
    rw [← Real.rpow_mul hx]
    norm_num
  have hroot : ∀ x : ℝ, 0 ≤ x → (x ^ 3) ^ (1 / 3 : ℝ) = x := by
    intro x hx
    rw [← Real.rpow_natCast x 3]
    rw [← Real.rpow_mul hx]
    norm_num
  have hmain : κ ^ 2 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) = 2 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := by
    have hL3 : (κ ^ 2 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)) ^ 3 = 2 * B * κ ^ 4 := by
      rw [mul_pow, hcube (2 * B / κ ^ 2) (by positivity)]
      field_simp
    have hR3 : (2 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ)) ^ 3 = 2 * B * κ ^ 4 := by
      rw [mul_pow, hcube (B * κ ^ 4 / 4) (by positivity)]
      ring
    have hnn1 : 0 ≤ κ ^ 2 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) := by positivity
    have hnn2 : 0 ≤ 2 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := by positivity
    calc κ ^ 2 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)
        = ((κ ^ 2 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)) ^ 3) ^ (1 / 3 : ℝ) :=
          (hroot _ hnn1).symm
      _ = (2 * B * κ ^ 4) ^ (1 / 3 : ℝ) := by rw [hL3]
      _ = ((2 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ)) ^ 3) ^ (1 / 3 : ℝ) := by rw [hR3]
      _ = 2 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := hroot _ hnn2
  have key : (κ ^ 2 / 2) * (3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2) =
      3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 - C := by
    have e1 : (κ ^ 2 / 2) * (3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ)) =
        3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) := by
      nlinarith [hmain]
    have e2 : (κ ^ 2 / 2) * (B / 6) = B / 12 * κ ^ 2 := by ring
    have e3 : (κ ^ 2 / 2) * (2 * C / κ ^ 2) = C := by
      field_simp
    rw [mul_sub, mul_sub, e1, e2, e3]
  constructor
  · intro h
    have h2 : 0 ≤ (κ ^ 2 / 2) * (3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2) :=
      mul_nonneg (by positivity) h
    rw [key] at h2
    linarith
  · intro h
    have hpos : 0 < κ ^ 2 / 2 := by linarith
    have h2 : 0 ≤ 3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 - C := by linarith
    rw [← key] at h2
    nlinarith [h2, hpos]
