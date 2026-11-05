-- Prove2me | solution 1 for LL_Decomp1543a.dyadic_invsqrt_sum
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:29.897147+00:00
-- url     : https://prove2.me/submissions/904d28eb-3eb4-4c93-a90a-9bb9aa0e7b43

import Mathlib

open Real Finset ArithmeticFunction

theorem solution (V : ℝ) (hV : 0 < V) (J : ℕ) :
    ∑ j ∈ range J, 1 / √(2 ^ j * V) ≤ (2 + √2) / √V := by
  have h2 : (0:ℝ) < √2 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : 1 < √2 := by nlinarith
  have hV' : 0 < √V := Real.sqrt_pos.2 hV
  have key : ∀ j : ℕ, 1 / √(2 ^ j * V) = (1 / √V) * (1 / √2) ^ j := by
    intro j
    have e : √((2:ℝ) ^ j) = √2 ^ j := by
      rw [show (2:ℝ) ^ j = (√2 ^ j) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
      exact Real.sqrt_sq (by positivity)
    rw [Real.sqrt_mul (by positivity), e, div_pow, one_pow, one_div_mul_one_div, mul_comm (√V)]
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have hr : 1 / √2 < 1 := by rw [div_lt_one h2]; exact h1
  have hr0 : 0 < 1 / √2 := by positivity
  rw [geom_sum_eq hr.ne]
  have hb : ((1 / √2) ^ J - 1) / (1 / √2 - 1) ≤ 2 + √2 := by
    rw [div_le_iff_of_neg (by linarith)]
    have : (2 + √2) * (1 / √2 - 1) = -1 := by field_simp; nlinarith
    have := pow_nonneg hr0.le J
    nlinarith
  calc 1 / √V * (((1 / √2) ^ J - 1) / (1 / √2 - 1)) ≤ 1 / √V * (2 + √2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 + √2) / √V := by ring
