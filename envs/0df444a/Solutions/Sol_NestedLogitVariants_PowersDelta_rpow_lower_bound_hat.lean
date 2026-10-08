-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.rpow_lower_bound_hat
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:21:00.857867+00:00
-- url     : https://prove2.me/submissions/550f7baf-96b1-4999-a8fb-2dcdda511661

import Mathlib

set_option autoImplicit false

theorem solution (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    (δ ^ l) ^ (γ - 1) * δ ^ (-max (γ - 1) 0) ≤ a ^ (γ - 1) := by
  have hδ0 : 0 < δ := lt_trans zero_lt_one hδ
  have hz : 0 < δ ^ (l - 1) := zpow_pos hδ0 _
  have ha0 : 0 < a := lt_of_lt_of_le hz ha1
  by_cases hg : 0 ≤ γ - 1
  · rw [max_eq_left hg]
    calc
      (δ ^ l) ^ (γ - 1) * δ ^ (-(γ - 1)) =
          (δ ^ (l - 1)) ^ (γ - 1) := by
        rw [← Real.rpow_intCast δ l, ← Real.rpow_mul hδ0.le,
          ← Real.rpow_add hδ0, ← Real.rpow_intCast δ (l - 1),
          ← Real.rpow_mul hδ0.le]
        congr 1
        push_cast
        ring
      _ ≤ a ^ (γ - 1) := Real.rpow_le_rpow hz.le ha1 hg
  · have hg' : γ - 1 ≤ 0 := le_of_not_ge hg
    rw [max_eq_right hg', neg_zero, Real.rpow_zero, mul_one]
    exact Real.rpow_le_rpow_of_nonpos ha0 ha2 hg'
