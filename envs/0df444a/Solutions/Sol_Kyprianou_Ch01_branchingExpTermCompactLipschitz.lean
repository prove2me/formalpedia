-- Prove2me | solution 1 for Kyprianou.Ch01.branchingExpTermCompactLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:21:17.403803+00:00
-- url     : https://prove2.me/submissions/5e2644bc-242d-41d7-a883-f2db1f2d9808

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_exp_lipschitz_below_upper
import Theorems.Thm_Kyprianou_Ch01_exp_uniform_lipschitz_on_positive
open Kyprianou.Ch01 Real Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (k : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |Real.exp (-y * ((k : ℝ) - 1)) -
      Real.exp (-x * ((k : ℝ) - 1))| ≤
      (a⁻¹ + Real.exp b) * |y - x| := by
  cases k with
  | zero =>
      have h := Kyprianou.Ch01.exp_lipschitz_below_upper b x y hx.2 hy.2
      have hC : Real.exp b ≤ a⁻¹ + Real.exp b :=
        le_add_of_nonneg_left (inv_nonneg.mpr ha.le)
      have hM := mul_le_mul_of_nonneg_right hC (abs_nonneg (y - x))
      simpa only [Nat.cast_zero] using le_trans (by simpa using h) hM
  | succ n =>
      have h := Kyprianou.Ch01.exp_uniform_lipschitz_on_positive
        a ha n x y hx.1 hy.1
      have hC : a⁻¹ ≤ a⁻¹ + Real.exp b :=
        le_add_of_nonneg_right (Real.exp_pos b).le
      have hM := mul_le_mul_of_nonneg_right hC (abs_nonneg (y - x))
      have heq : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by
        push_cast
        ring
      simpa only [heq] using le_trans h hM

