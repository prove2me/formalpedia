-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.summable_exp_neg_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:06:30.333955+00:00
-- url     : https://prove2.me/submissions/8453edef-65d1-4b3e-afff-b0d2d475bfdc

import Mathlib


theorem solution {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  have H : Summable fun n : ℕ => Real.exp ((-c) * (n:ℝ)^2) := by
    apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hc)
    intro i
    exact_mod_cast (show i ≤ i^2 by cases i with | zero => simp | succ k => rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k) )
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [neg_mul,neg_sq] using H
