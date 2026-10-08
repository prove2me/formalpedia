-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.exponent_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:21:08.377726+00:00
-- url     : https://prove2.me/submissions/507704d4-fc0d-4b9f-83b0-34c55d758ae7

import Mathlib

set_option autoImplicit false

theorem solution (δ γ γbar : ℝ) (hδ : 1 < δ) (hγ : 0 < γ) (hγle : γ ≤ γbar)
    (hγbar1 : 1 < γbar) :
    1 ≤ δ ^ γbar * δ ^ (-max (γ - 1) 0) * δ ^ (-max (1 - γ) 0) ∧
      δ ^ (γbar + γ + 1) ≤ δ ^ (2 * γbar + 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  constructor
  · rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    have he : 0 ≤ γbar + -max (γ - 1) 0 + -max (1 - γ) 0 := by
      by_cases hg : 1 ≤ γ
      · rw [max_eq_left (by linarith : 0 ≤ γ - 1),
          max_eq_right (by linarith : 1 - γ ≤ 0)]
        linarith
      · rw [max_eq_right (by linarith : γ - 1 ≤ 0),
          max_eq_left (by linarith : 0 ≤ 1 - γ)]
        linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hδ.le he
  · exact Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
