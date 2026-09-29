-- Prove2me | solution 1 for KLZ97.overhead_polylog
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:47:35.290758+00:00
-- url     : https://prove2.me/submissions/e63f2a6f-cb8a-4e8b-a1da-45efac1f1919

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

theorem solution (K L : ℝ) (hK : 2 ≤ K) (hL : 1 ≤ L) :
    K ^ (⌈Real.logb 2 L⌉₊) ≤ K * L ^ Real.logb 2 K := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hlb : 0 ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) hL
  have hc : (⌈Real.logb 2 L⌉₊ : ℝ) ≤ Real.logb 2 L + 1 := (Nat.ceil_lt_add_one hlb).le
  have h1 : K ^ (⌈Real.logb 2 L⌉₊) ≤ K ^ (Real.logb 2 L + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK1 hc
  have h2 : K ^ (Real.logb 2 L + 1) = K * L ^ Real.logb 2 K := by
    rw [Real.rpow_add hK0, Real.rpow_one, mul_comm]
    congr 1
    rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hL0, Real.logb, Real.logb]
    congr 1; ring
  exact h1.trans h2.le
