-- Prove2me | solution 1 for Maldacena2003.shapeF_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:03:08.209992+00:00
-- url     : https://prove2.me/submissions/66988180-0928-4bff-95c5-1925dd5fbee2

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem sf_bounds (k₁ k₂ k₃ : ℝ) (hk : IsMomentumTriangle k₁ k₂ k₃) :
    0 ≤ shapeF k₁ k₂ k₃ ∧ shapeF k₁ k₂ k₃ ≤ 5 / 6 := by
  obtain ⟨h1, h2, h3, t1, t2, t3⟩ := hk
  have hS : 0 < k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3 := by positivity
  have hT : 0 < k₁ + k₂ + k₃ := by positivity
  simp only [shapeF, shapeBracket]
  constructor
  · rw [sub_nonneg, le_div_iff₀ hS]
    have : 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) / (k₁ + k₂ + k₃)
        = 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) / (k₁ + k₂ + k₃) := rfl
    rw [← sub_nonneg]
    have key : 0 ≤ ((1 / 2) * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)
      + (1 / 2) * (k₁ * k₂ ^ 2 + k₁ * k₃ ^ 2 + k₂ * k₁ ^ 2 + k₂ * k₃ ^ 2 + k₃ * k₁ ^ 2 + k₃ * k₂ ^ 2)
      - 2 * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)) * (k₁ + k₂ + k₃)
      + 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 t1) (sub_nonneg.2 t2)) (sub_nonneg.2 t3),
        mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3, mul_pos (mul_pos h1 h2) h3,
        mul_nonneg (mul_nonneg (sub_nonneg.2 t1) (sub_nonneg.2 t2)) h3.le,
        mul_nonneg (mul_nonneg (sub_nonneg.2 t2) (sub_nonneg.2 t3)) h1.le,
        mul_nonneg (mul_nonneg (sub_nonneg.2 t1) (sub_nonneg.2 t3)) h2.le,
        sq_nonneg (k₁ - k₂), sq_nonneg (k₂ - k₃), sq_nonneg (k₁ - k₃)]
    have e : 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) / (k₁ + k₂ + k₃)
      = (4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2)) / (k₁ + k₂ + k₃) := rfl
    have := div_nonneg key hT.le
    rw [add_div, mul_div_cancel_right₀ _ hT.ne'] at this
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hS]
    have key : 0 ≤ ((17 / 6) * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3) - (1 / 2) * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)
      - (1 / 2) * (k₁ * k₂ ^ 2 + k₁ * k₃ ^ 2 + k₂ * k₁ ^ 2 + k₂ * k₃ ^ 2 + k₃ * k₁ ^ 2 + k₃ * k₂ ^ 2)) * (k₁ + k₂ + k₃)
      - 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) := by
      nlinarith [mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3, mul_pos (mul_pos h1 h2) h3,
        mul_nonneg (mul_nonneg h1.le h2.le) (sq_nonneg (k₁ - k₂)),
        mul_nonneg (mul_nonneg h2.le h3.le) (sq_nonneg (k₂ - k₃)),
        mul_nonneg (mul_nonneg h1.le h3.le) (sq_nonneg (k₁ - k₃)),
        mul_nonneg (add_pos h1 h2).le (sq_nonneg (k₁ - k₂)),
        mul_nonneg h3.le (sq_nonneg (k₁ - k₂)), mul_nonneg h1.le (sq_nonneg (k₂ - k₃)),
        mul_nonneg h2.le (sq_nonneg (k₁ - k₃)),
        sq_nonneg (k₁ - k₂), sq_nonneg (k₂ - k₃), sq_nonneg (k₁ - k₃)]
    have := div_nonneg key hT.le
    rw [sub_div, mul_div_cancel_right₀ _ hT.ne'] at this
    linarith

theorem solution (k₁ k₂ k₃ : ℝ) (hk : IsMomentumTriangle k₁ k₂ k₃) :
    0 ≤ shapeF k₁ k₂ k₃ ∧ shapeF k₁ k₂ k₃ ≤ 5 / 6 := sf_bounds k₁ k₂ k₃ hk
