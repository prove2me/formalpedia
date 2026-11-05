-- Prove2me | solution 1 for LL_Decomp1543a.dyadic_sqrt_sum
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:30.507712+00:00
-- url     : https://prove2.me/submissions/9da0d7cf-0fe1-454c-8585-9f907ada8945

import Mathlib

open Real Finset ArithmeticFunction

theorem solution (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (J : ℕ) (hJ : 1 ≤ J)
    (hJV : 2 ^ (J - 1) * V ≤ N / U) :
    ∑ j ∈ range J, √(2 ^ j * V) ≤ (2 + √2) * √(N / U) := by
  have h2 : (0:ℝ) < √2 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : 1 < √2 := by nlinarith
  have hV' : 0 < √V := Real.sqrt_pos.2 hV
  have pw : ∀ j : ℕ, √((2:ℝ) ^ j) = √2 ^ j := by
    intro j
    rw [show (2:ℝ) ^ j = (√2 ^ j) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
    exact Real.sqrt_sq (by positivity)
  have key : ∀ j : ℕ, √(2 ^ j * V) = √V * √2 ^ j := by
    intro j
    rw [Real.sqrt_mul (by positivity), pw]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum, geom_sum_eq h1.ne']
  have hJ' : J = (J - 1) + 1 := by omega
  have hb : (√2 ^ J - 1) / (√2 - 1) ≤ √2 ^ (J - 1) * (2 + √2) := by
    rw [div_le_iff₀ (by linarith)]
    have e : √2 ^ (J - 1) * (2 + √2) * (√2 - 1) = √2 ^ (J - 1) * √2 := by
      have : (2 + √2) * (√2 - 1) = √2 := by nlinarith
      rw [mul_assoc, this]
    rw [e]
    conv_lhs => rw [hJ', pow_succ]
    linarith
  have hs : √V * √2 ^ (J - 1) ≤ √(N / U) := by
    rw [← pw, ← Real.sqrt_mul hV.le, mul_comm]
    exact Real.sqrt_le_sqrt hJV
  calc √V * ((√2 ^ J - 1) / (√2 - 1)) ≤ √V * (√2 ^ (J - 1) * (2 + √2)) :=
        mul_le_mul_of_nonneg_left hb hV'.le
    _ = (√V * √2 ^ (J - 1)) * (2 + √2) := by ring
    _ ≤ √(N / U) * (2 + √2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = (2 + √2) * √(N / U) := by ring
