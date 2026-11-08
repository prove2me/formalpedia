-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:56:08.108597+00:00
-- url     : https://prove2.me/submissions/fed3ba43-c43d-4351-a239-1ab55664546d

import Mathlib

theorem solution (δ : ℝ) (hδ : 1 < δ) (γ γbar : ℝ) (hγ : 0 ≤ γ) (hγle : γ ≤ γbar)
    (hγbar : 1 < γbar) :
    1 ≤ δ ^ γbar * δ ^ (-(max (γ - 1) 0)) * δ ^ (-(max (1 - γ) 0)) ∧
      δ ^ (γbar + γ + 1) ≤ δ ^ (2 * γbar + 1) := by
  have hδ0 : 0 < δ := by linarith
  constructor
  · rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    apply Real.one_le_rpow hδ.le
    rcases le_total γ 1 with h | h
    · rw [max_eq_right (by linarith : γ - 1 ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ 1 - γ)]
      linarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ γ - 1), max_eq_right (by linarith : 1 - γ ≤ 0)]
      linarith
  · exact Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
