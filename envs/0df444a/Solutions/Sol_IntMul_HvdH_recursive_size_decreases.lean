-- Prove2me | solution 1 for IntMul.HvdH.recursive_size_decreases
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T14:35:31.009826+00:00
-- url     : https://prove2.me/submissions/8a0bb0d5-95de-4be7-97d1-c29c238e0f14

import Definitions.Def_IntMul_HvdH_StepParameters
import Mathlib.Tactic

open IntMul.HvdH

private lemma chunk_square_bound (b : ℕ) (hb : 30 ≤ b) :
    1296 * b ^ 2 < 2 ^ (b - 1) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = (k - 1) + 1 by omega,
      show (2 : ℕ) ^ (k - 1 + 1) = 2 ^ (k - 1) * 2 from pow_succ 2 (k - 1)]
    nlinarith

/-- Every recursive input is positive and strictly smaller than the original input. -/
theorem solution (d n b p T r : ℕ) (hd : 2 ≤ d)
    (h : StepParameters d n b p T r) : 1 ≤ 3 * r * p ∧ 3 * r * p < n := by
  rcases h with ⟨hn, hb, hp, hTpow, hT1, hT2, hrpow, hr1, hr2⟩
  have hd0 : 0 < d := by omega
  have hd12 : 4096 ≤ d ^ 12 := by
    have hh := Nat.pow_le_pow_left hd 12
    norm_num at hh
    exact hh
  have hbd : d ^ 12 ≤ b := by
    rw [hb, ← Nat.clog_pow 2 (d ^ 12) (by norm_num)]
    exact Nat.clog_mono_right 2 hn
  have hb4096 : 4096 ≤ b := hd12.trans hbd
  have hn2 : 2 ≤ n :=
    le_trans (Nat.succ_le_of_lt
      (Nat.one_lt_two_pow (by positivity) : 1 < 2 ^ (d ^ 12))) hn
  have hbR : (4096 : ℝ) ≤ b := by exact_mod_cast hb4096
  have hbpos : (0 : ℝ) < b := by linarith
  obtain ⟨k, hk⟩ := hTpow
  have hTge : (1 : ℝ) ≤ T := by rw [hk]; exact_mod_cast Nat.one_le_two_pow
  have hTb : (T : ℝ) * b < 8 * n := by rwa [lt_div_iff₀ hbpos] at hT2
  have hTn : (T : ℝ) < n := by nlinarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (T : ℝ) ^ ((1 : ℝ) / d) ≤ Real.sqrt n := by
    have hh : (1 : ℝ) / d ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < d) (by norm_num)).mpr
      linarith
    calc
      (T : ℝ) ^ ((1 : ℝ) / d) ≤ (T : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hTge hh
      _ = Real.sqrt T := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hTn.le
  have hsq : (36 * (b : ℝ)) ^ 2 ≤ n := by
    have hh := chunk_square_bound b (by omega)
    have hh' := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
    rw [← hb] at hh'
    have hnat : (36 * b) ^ 2 < n := by
      calc
        (36 * b) ^ 2 = 1296 * b ^ 2 := by ring
        _ < 2 ^ (b - 1) := hh
        _ = 2 ^ b.pred := rfl
        _ < n := hh'
    exact_mod_cast hnat.le
  have hchunk : 36 * (b : ℝ) ≤ Real.sqrt n := by
    have hh := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hh
  obtain ⟨j, hj⟩ := hrpow
  have hrge : 1 ≤ r := by rw [hj]; exact Nat.one_le_two_pow
  have hpge : 1 ≤ p := by omega
  have hmR : ((3 * r * p : ℕ) : ℝ) < n := by
    calc
      ((3 * r * p : ℕ) : ℝ) = 18 * b * r := by rw [hp]; push_cast; ring
      _ < 18 * b * (2 * (T : ℝ) ^ ((1 : ℝ) / d)) :=
        mul_lt_mul_of_pos_left hr2 (by positivity)
      _ = (36 * b : ℝ) * (T : ℝ) ^ ((1 : ℝ) / d) := by ring
      _ ≤ (36 * b : ℝ) * Real.sqrt n := by gcongr
      _ ≤ Real.sqrt n * Real.sqrt n := by gcongr
      _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  constructor
  · have hh : 0 < 3 * r * p := by positivity
    omega
  · exact_mod_cast hmR


