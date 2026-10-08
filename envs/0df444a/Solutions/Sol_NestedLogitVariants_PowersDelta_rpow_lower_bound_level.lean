-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.rpow_lower_bound_level
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:21:04.546122+00:00
-- url     : https://prove2.me/submissions/eb0cc704-fb00-4757-a1d7-bc438dfe0fef

import Mathlib

set_option autoImplicit false

theorem solution (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    δ ^ (-max (1 - γ) 0) * a ^ (γ - 1) ≤ (δ ^ l) ^ (γ - 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  have hz : 0 < δ ^ (l - 1) := zpow_pos hδ0 _
  have ha0 : 0 < a := lt_of_lt_of_le hz ha1
  by_cases hg : 0 ≤ γ - 1
  · rw [max_eq_right (by linarith : 1 - γ ≤ 0), neg_zero, Real.rpow_zero, one_mul]
    exact Real.rpow_le_rpow ha0.le ha2 hg
  · have hg' : γ - 1 ≤ 0 := le_of_not_ge hg
    rw [max_eq_left (by linarith : 0 ≤ 1 - γ)]
    calc
      δ ^ (-(1 - γ)) * a ^ (γ - 1) ≤
          δ ^ (-(1 - γ)) * (δ ^ (l - 1)) ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz ha1 hg')
          (Real.rpow_nonneg hδ0.le _)
      _ = (δ ^ l) ^ (γ - 1) := by
        rw [← Real.rpow_intCast δ (l - 1), ← Real.rpow_mul hδ0.le,
          ← Real.rpow_add hδ0, ← Real.rpow_intCast δ l,
          ← Real.rpow_mul hδ0.le]
        congr 1
        push_cast
        ring
