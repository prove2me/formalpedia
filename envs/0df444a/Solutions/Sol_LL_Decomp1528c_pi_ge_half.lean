-- Prove2me | solution 1 for LL_Decomp1528c.pi_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:11.007021+00:00
-- url     : https://prove2.me/submissions/4a47b282-ff35-4a11-9ced-2c66970d2120

import Mathlib

open Real Finset Chebyshev

theorem solution {x : ℝ} (hx : 11 ≤ x) : x / (2 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  set n := ⌊x⌋₊ with hn
  have hn11 : 11 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnr : (11 : ℝ) ≤ n := by exact_mod_cast hn11
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogx : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlx : 0 < Real.log x := by linarith
  have hl1 := Real.log_two_gt_d9
  rcases lt_or_ge n 19 with h20 | h20
  · -- small range
    have h5 : (5 : ℝ) ≤ (Nat.primeCounting n : ℝ) := by
      have : Nat.primeCounting 11 = 5 := by decide
      have h := Nat.monotone_primeCounting hn11
      rw [this] at h
      exact_mod_cast h
    have hl11 : 2 ≤ Real.log 11 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h1]
      calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 2
        _ ≤ 11 := by norm_num
    have hlx2 : 2 ≤ Real.log x := le_trans hl11 (Real.log_le_log (by norm_num) hx)
    have hn20 : (n : ℝ) < 19 := by exact_mod_cast h20
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have hn20 : (19 : ℝ) ≤ n := by exact_mod_cast h20
    have hp := Chebyshev.pi_ge n
    have ht : Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / 16 + 4 * Real.log 2 - 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / 16 by positivity)
      rw [Real.log_div (by positivity) (by norm_num),
        show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
      push_cast at this
      linarith
    have h1 : ((n : ℝ) + 1) / 2 ≤ n * Real.log 2 - Real.log ((n : ℝ) + 1) := by
      nlinarith
    have h2 : x / (2 * Real.log x) ≤ ((n : ℝ) + 1) / 2 / Real.log n := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine h2.trans (le_trans ?_ hp)
    exact div_le_div_of_nonneg_right h1 hlogn.le
