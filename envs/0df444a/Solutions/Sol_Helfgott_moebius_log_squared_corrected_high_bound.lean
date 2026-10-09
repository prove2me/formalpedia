-- Prove2me | solution 1 for Helfgott.moebius_log_squared_corrected_high_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:27:55.304107+00:00
-- url     : https://prove2.me/submissions/566ca9af-e5bf-4d97-a67d-bb815bc04774

import Theorems.Thm_Helfgott_moebius_log_squared_two_range_hyperbola_bound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma hyperbola_floor_ratio_log_bound (N K0 K1 : ℕ)
    (hK0 : 0 < K0) (hK01 : K0 ≤ K1) (hH1 : 0 < N / K1) :
    Real.log (((N / K0 : ℕ) : ℝ) / ((N / K1 : ℕ) : ℝ)) ≤
      Real.log ((K1 : ℝ) / (K0 : ℝ)) + 1 / ((N / K1 : ℕ) : ℝ) := by
  have hK1 : 0 < K1 := hK0.trans_le hK01
  have hK0r : (0 : ℝ) < K0 := by exact_mod_cast hK0
  have hK1r : (0 : ℝ) < K1 := by exact_mod_cast hK1
  have hH01 : N / K1 ≤ N / K0 := Nat.div_le_div_left hK01 hK0
  have hH0r : (0 : ℝ) < (N / K0 : ℕ) := by exact_mod_cast (hH1.trans_le hH01)
  have hH1r : (0 : ℝ) < (N / K1 : ℕ) := by exact_mod_cast hH1
  have hlow : ((N / K0 : ℕ) : ℝ) * (K0 : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N K0
  have hhigh : (N : ℝ) < (K1 : ℝ) * (((N / K1 : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hK1
  have hr : ((N / K0 : ℕ) : ℝ) / ((N / K1 : ℕ) : ℝ) ≤
      ((K1 : ℝ) / (K0 : ℝ)) * (1 + 1 / ((N / K1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ hH1r).mpr
    have he : ((K1 : ℝ) / (K0 : ℝ)) * (1 + 1 / ((N / K1 : ℕ) : ℝ)) *
        ((N / K1 : ℕ) : ℝ) =
        ((K1 : ℝ) * (((N / K1 : ℕ) : ℝ) + 1)) / (K0 : ℝ) := by
      field_simp
    rw [he]
    apply (le_div_iff₀ hK0r).mpr
    linarith
  have hl := Real.log_le_log (div_pos hH0r hH1r) hr
  rw [Real.log_mul (div_pos hK1r hK0r).ne' (by positivity : (0 : ℝ) < 1 + 1 / ((N / K1 : ℕ) : ℝ)).ne'] at hl
  have hone := Real.log_le_sub_one_of_pos
    (by positivity : (0 : ℝ) < 1 + 1 / ((N / K1 : ℕ) : ℝ))
  linarith

lemma corrected_high_log_ten_lower : (23 / 10 : ℝ) ≤ Real.log 10 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

lemma corrected_high_density_upper : (6 / Real.pi ^ 2 : ℝ) ≤ 61 / 100 := by
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith [Real.pi_gt_d2]

lemma corrected_high_log_ratio_upper :
    Real.log ((10000000000000000 : ℝ) / 21000000000) ≤ 13123 / 1000 := by
  have hm := Real.log_le_log
    (by norm_num : (0 : ℝ) < 10000000000000000 / 21000000000)
    (by norm_num : (10000000000000000 : ℝ) / 21000000000 ≤ 500000)
  have hl : Real.log (500000 : ℝ) ≤ 13123 / 1000 := by
    rw [show (500000 : ℝ) = 5 * 10 ^ (5 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
      show Real.log (10 : ℝ) = Real.log 2 + Real.log 5 by
        rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  exact hm.trans hl

theorem corrected_high_two_range_numeric_bound (N : ℕ) (C : ℝ)
    (hN : 100000000000000000000000000 ≤ N) (hC : |C| ≤ 2) :
    |C| + (N : ℝ) *
      ((65 / 10000) * ((6 / Real.pi ^ 2) * Real.log ((N : ℝ) / 10000000000000000) + 583 / 500) +
       (31 / 1000) * ((6 / Real.pi ^ 2) * Real.log
         (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) +
         9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
         (6 / Real.pi ^ 2) / ((N / 10000000000000000 : ℕ) : ℝ)) + 1 / 4) ≤
      (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := by
  have hNr : (100000000000000000000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hH : 10000000000 ≤ N / 10000000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa using hN)
  have hHr : (10000000000 : ℝ) ≤ ((N / 10000000000000000 : ℕ) : ℝ) := by exact_mod_cast hH
  have hHp : (0 : ℝ) < ((N / 10000000000000000 : ℕ) : ℝ) := by linarith
  have hρ0 : (0 : ℝ) ≤ 6 / Real.pi ^ 2 := by positivity
  have hρ := corrected_high_density_upper
  have hlogN : (299 / 5 : ℝ) ≤ Real.log (N : ℝ) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 100000000000000000000000000) hNr
    rw [show (100000000000000000000000000 : ℝ) = 10 ^ (26 : ℕ) by norm_num, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith [corrected_high_log_ten_lower]
  have hlogK : (184 / 5 : ℝ) ≤ Real.log (10000000000000000 : ℝ) := by
    rw [show (10000000000000000 : ℝ) = 10 ^ (16 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [corrected_high_log_ten_lower]
  have hlogratio0 : 0 ≤ Real.log ((N : ℝ) / 10000000000000000) :=
    Real.log_nonneg ((le_div_iff₀ (by norm_num)).mpr (by linarith))
  have hhigh : (6 / Real.pi ^ 2) * Real.log ((N : ℝ) / 10000000000000000) + 583 / 500 ≤
      (61 / 100) * (Real.log (N : ℝ) - 184 / 5) + 583 / 500 := by
    have hm := mul_le_mul_of_nonneg_right hρ hlogratio0
    rw [Real.log_div hNp.ne' (by norm_num)] at hm ⊢
    nlinarith
  have hfloor := hyperbola_floor_ratio_log_bound N 21000000000 10000000000000000
    (by norm_num) (by norm_num) (by omega)
  have hlogmid : Real.log
      (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) ≤
      13123 / 1000 + 1 / ((N / 10000000000000000 : ℕ) : ℝ) := by
    have hl := corrected_high_log_ratio_upper
    norm_num only [Nat.cast_ofNat] at hfloor
    linarith
  have hmidmul : (6 / Real.pi ^ 2) * Real.log
      (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) ≤
      (61 / 100) * (13123 / 1000 + 1 / ((N / 10000000000000000 : ℕ) : ℝ)) := by
    calc
      _ ≤ (6 / Real.pi ^ 2) * (13123 / 1000 + 1 / ((N / 10000000000000000 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogmid hρ0
      _ ≤ _ := mul_le_mul_of_nonneg_right hρ (by positivity)
  have hdivρ : (6 / Real.pi ^ 2) / ((N / 10000000000000000 : ℕ) : ℝ) ≤
      (61 / 100) / ((N / 10000000000000000 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hρ hHp.le
  have hsqrt : (100000 : ℝ) ≤ Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by nlinarith)
  have hsqrp : 0 < Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) := by linarith
  have hs : 9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) ≤ (9 / 100000 : ℝ) := by
    apply (div_le_iff₀ hsqrp).mpr
    nlinarith
  have hd : (122 / 100) / ((N / 10000000000000000 : ℕ) : ℝ) ≤ (1 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hsmall : 9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
      (122 / 100) / ((N / 10000000000000000 : ℕ) : ℝ) ≤ (1 / 10000 : ℝ) := by linarith
  have hmiddle : (6 / Real.pi ^ 2) * Real.log
      (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) +
      9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
      (6 / Real.pi ^ 2) / ((N / 10000000000000000 : ℕ) : ℝ) ≤
      (61 / 100) * (13123 / 1000) + 1 / 10000 := by
    calc
      _ ≤ (61 / 100) * (13123 / 1000 + 1 / ((N / 10000000000000000 : ℕ) : ℝ)) +
          9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
          (61 / 100) / ((N / 10000000000000000 : ℕ) : ℝ) := by linarith
      _ = (61 / 100) * (13123 / 1000) +
          (9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
            (122 / 100) / ((N / 10000000000000000 : ℕ) : ℝ)) := by ring
      _ ≤ _ := by linarith
  have hinner : (65 / 10000) *
      ((6 / Real.pi ^ 2) * Real.log ((N : ℝ) / 10000000000000000) + 583 / 500) +
      (31 / 1000) * ((6 / Real.pi ^ 2) * Real.log
        (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) +
        9 / Real.sqrt ((N / 10000000000000000 : ℕ) : ℝ) +
        (6 / Real.pi ^ 2) / ((N / 10000000000000000 : ℕ) : ℝ)) + 1 / 4 + 1 / 10000 ≤
      (7 / 500) * Real.log (N : ℝ) - 23 / 100 := by
    have hhi := mul_le_mul_of_nonneg_left hhigh (by norm_num : (0 : ℝ) ≤ 65 / 10000)
    have hmi := mul_le_mul_of_nonneg_left hmiddle (by norm_num : (0 : ℝ) ≤ 31 / 1000)
    nlinarith
  have hC' : |C| ≤ (N : ℝ) / 10000 := by linarith
  have hf := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg N)
  nlinarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem moebius_log_squared_corrected_high_bound_complete (N : ℕ) (C : ℝ)
    (hN : 100000000000000000000000000 ≤ N) (hC : |C| ≤ 2)
    (hRhigh : ∀ d ∈ Icc 1 (N / 10000000000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * ((N : ℝ) / (d : ℝ)))
    (hRmiddle : ∀ d ∈ Ioc (N / 10000000000000000) (N / 21000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, 2160535 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345)
    (hfinite :
      ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := by
  have hH1 : 10000 ≤ N / 10000000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by norm_num; omega)
  have hH0 : 2160535 ≤ N / 21000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by norm_num; omega)
  have hM' : ∀ u : ℕ, N / 21000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345 := by
    intro u hu
    exact hM u (hH0.trans hu)
  have hf :
      ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ (4345 : ℝ) * (1 / 4) := by
    convert hfinite using 1 <;> ring
  have hb := moebius_log_squared_two_range_hyperbola_bound N 21000000000 10000000000000000
    C 4345 (31 / 1000) (65 / 10000) (1 / 4)
    (by norm_num) (by norm_num) hH1 (by norm_num) (by norm_num) (by norm_num)
    hRhigh hRmiddle hM' hf
  norm_num only [Nat.cast_ofNat] at hb
  have hn := corrected_high_two_range_numeric_bound N C hN hC
  norm_num only [Nat.cast_ofNat] at hn
  exact hb.trans hn

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (N : ℕ) (C : ℝ)
    (hN : 100000000000000000000000000 ≤ N) (hC : |C| ≤ 2)
    (hRhigh : ∀ d ∈ Icc 1 (N / 10000000000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * ((N : ℝ) / (d : ℝ)))
    (hRmiddle : ∀ d ∈ Ioc (N / 10000000000000000) (N / 21000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, 2160535 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345)
    (hfinite :
      ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := Helfgott.moebius_log_squared_corrected_high_bound_complete N C hN hC hRhigh hRmiddle hM hfinite
#print axioms solution
