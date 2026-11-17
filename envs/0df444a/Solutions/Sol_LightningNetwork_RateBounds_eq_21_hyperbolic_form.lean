-- Prove2me | solution 1 for LightningNetwork.RateBounds.eq_21_hyperbolic_form
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:43:37.52324+00:00
-- url     : https://prove2.me/submissions/fae37d35-7f52-4791-b226-91ea67eef2b3

import Mathlib

theorem solution (κ B C m : ℝ) (hκ : 0 < κ) (hm : 0 < m) :
    2 * m + 2 * B * Real.exp κ ^ m / (Real.exp κ ^ m - 1) ^ 2
        - 2 * C * Real.exp κ / (Real.exp κ - 1) ^ 2
      = 2 * m + B / 2 * (1 / Real.sinh (κ * m / 2) ^ 2)
        - C / 2 * (1 / Real.sinh (κ / 2) ^ 2) := by
  have hsinh : ∀ y : ℝ, 1 / Real.sinh y ^ 2 = 4 * Real.exp y ^ 2 / (Real.exp y ^ 2 - 1) ^ 2 := by
    intro y
    have hE : Real.exp y ≠ 0 := ne_of_gt (Real.exp_pos y)
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp
    ring
  have h1 : 1 / Real.sinh (κ * m / 2) ^ 2 = 4 * Real.exp (κ * m) / (Real.exp (κ * m) - 1) ^ 2 := by
    rw [hsinh]
    have hsq : Real.exp (κ * m / 2) ^ 2 = Real.exp (κ * m) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
  have h2 : 1 / Real.sinh (κ / 2) ^ 2 = 4 * Real.exp κ / (Real.exp κ - 1) ^ 2 := by
    rw [hsinh]
    have hsq : Real.exp (κ / 2) ^ 2 = Real.exp κ := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
  have hm1 : Real.exp κ ^ m = Real.exp (κ * m) := (Real.exp_mul κ m).symm
  rw [h1, h2, hm1]
  ring
