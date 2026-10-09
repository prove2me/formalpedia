-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_high_of_prime_errors_and_tail_mertens
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:47:14.465071+00:00
-- url     : https://prove2.me/submissions/46494436-11e8-4285-8480-abeff1f5e53f

import Theorems.Thm_Helfgott_moebius_log_squared_two_range_hyperbola_bound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_Helfgott_centered_prime_finite_moment_twenty_one_billion
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma reciprocal_tail_high_hyperbola_floor_ratio_log_bound (N K0 K1 : ℕ)
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

lemma reciprocal_tail_high_corrected_high_log_ten_lower : (23 / 10 : ℝ) ≤ Real.log 10 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

lemma reciprocal_tail_high_corrected_high_density_upper : (6 / Real.pi ^ 2 : ℝ) ≤ 61 / 100 := by
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith [Real.pi_gt_d2]

lemma reciprocal_tail_high_corrected_high_log_ratio_upper :
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

theorem reciprocal_tail_high_corrected_high_two_range_numeric_bound (N : ℕ) (C : ℝ)
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
  have hρ := reciprocal_tail_high_corrected_high_density_upper
  have hlogN : (299 / 5 : ℝ) ≤ Real.log (N : ℝ) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 100000000000000000000000000) hNr
    rw [show (100000000000000000000000000 : ℝ) = 10 ^ (26 : ℕ) by norm_num, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith [reciprocal_tail_high_corrected_high_log_ten_lower]
  have hlogK : (184 / 5 : ℝ) ≤ Real.log (10000000000000000 : ℝ) := by
    rw [show (10000000000000000 : ℝ) = 10 ^ (16 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [reciprocal_tail_high_corrected_high_log_ten_lower]
  have hlogratio0 : 0 ≤ Real.log ((N : ℝ) / 10000000000000000) :=
    Real.log_nonneg ((le_div_iff₀ (by norm_num)).mpr (by linarith))
  have hhigh : (6 / Real.pi ^ 2) * Real.log ((N : ℝ) / 10000000000000000) + 583 / 500 ≤
      (61 / 100) * (Real.log (N : ℝ) - 184 / 5) + 583 / 500 := by
    have hm := mul_le_mul_of_nonneg_right hρ hlogratio0
    rw [Real.log_div hNp.ne' (by norm_num)] at hm ⊢
    nlinarith
  have hfloor := reciprocal_tail_high_hyperbola_floor_ratio_log_bound N 21000000000 10000000000000000
    (by norm_num) (by norm_num) (by omega)
  have hlogmid : Real.log
      (((N / 21000000000 : ℕ) : ℝ) / ((N / 10000000000000000 : ℕ) : ℝ)) ≤
      13123 / 1000 + 1 / ((N / 10000000000000000 : ℕ) : ℝ) := by
    have hl := reciprocal_tail_high_corrected_high_log_ratio_upper
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

theorem reciprocal_tail_high_moebius_log_squared_corrected_high_of_tail_mertens (N : ℕ) (C : ℝ)
    (hN : 1000000000000000000000000000 ≤ N) (hC : |C| ≤ 2)
    (hRhigh : ∀ d ∈ Icc 1 (N / 10000000000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * ((N : ℝ) / (d : ℝ)))
    (hRmiddle : ∀ d ∈ Ioc (N / 10000000000000000) (N / 21000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, 10000000000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345)
 :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := by
  have hH1 : 10000 ≤ N / 10000000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by norm_num; omega)
  have hH0 : 10000000000000000 ≤ N / 21000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by norm_num; omega)
  have hM' : ∀ u : ℕ, N / 21000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345 := by
    intro u hu
    exact hM u (hH0.trans hu)
  have hb := moebius_log_squared_two_range_hyperbola_bound N 21000000000 10000000000000000
    C 4345 (31 / 1000) (65 / 10000) (1 / 4)
    (by norm_num) (by norm_num) hH1 (by norm_num) (by norm_num) (by norm_num)
    hRhigh hRmiddle hM' (by
      simpa only [Nat.cast_ofNat, div_eq_mul_inv, one_mul] using
        centered_prime_finite_moment_twenty_one_billion C hC)
  norm_num only [Nat.cast_ofNat] at hb
  have hn := reciprocal_tail_high_corrected_high_two_range_numeric_bound N C (by omega) hC
  norm_num only [Nat.cast_ofNat] at hn
  exact hb.trans hn

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_log_weight_sum_zero_remove (c : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d * Real.log (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, c d * Real.log (d : ℝ) ^ 2 := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, Real.log_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add]
  rfl

lemma reciprocal_tail_high_log_weight_sum_Ioc_difference (c : ℕ → ℝ) (A N : ℕ) (hAN : A ≤ N) :
    (∑ d ∈ Finset.Ioc A N, c d) =
      (∑ d ∈ Finset.Icc 1 N, c d) - ∑ d ∈ Finset.Icc 1 A, c d := by
  have h := Finset.sum_Ioc_consecutive c (Nat.zero_le A) hAN
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one, zero_add] at h
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one] at ⊢
  linarith

lemma reciprocal_tail_high_hasDerivAt_log_inv_sq (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (Real.log t ^ 2)⁻¹)
      (-(2 / (t * Real.log t ^ 3))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((Real.hasDerivAt_log ht0).pow 2).inv (pow_ne_zero 2 hl0)
  convert hd using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; field_simp [hl0, ht0]; ring)

lemma reciprocal_tail_high_log_weight_deriv_continuous (a x : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => -(2 / (t * Real.log t ^ 3))) (Set.Icc a x) := by
  have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by
    intro t ht; linarith [ht.1]
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => ht0 t ht)
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  exact (continuousOn_const.div (continuousOn_id.mul (hl.pow 3))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (hl0 t ht)))).neg

lemma reciprocal_tail_high_log_weight_kernel_intervalIntegrable (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x := by
  have hf : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 3)⁻¹) (Set.Icc a x) := by
    have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by intro t ht; linarith [ht.1]
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => ht0 t ht)
    exact (continuousOn_id.mul (hl.pow 3)).inv₀ (fun t ht =>
      mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
  have h := integrableOn_mul_sum_Icc (fun d => c d * Real.log (d : ℝ) ^ 2)
    (by linarith : 0 ≤ a) hf.integrableOn_Icc (m := 1)
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem reciprocal_tail_high_log_squared_weight_removal_identity (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) := by
  have hd : ∀ t ∈ Set.Icc a x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t ^ 2)⁻¹) t := by
    intro t ht; exact (reciprocal_tail_high_hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hdv : ∀ t ∈ Set.Icc a x,
      deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t = -(2 / (t * Real.log t ^ 3)) := by
    intro t ht; exact (reciprocal_tail_high_hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹)) (Set.Icc a x) :=
    ((reciprocal_tail_high_log_weight_deriv_continuous a x ha).integrableOn_Icc).congr_fun
      (fun t ht => (hdv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun d => c d * Real.log (d : ℝ) ^ 2) (by linarith : 0 ≤ a) hax hd hi
  simp_rw [reciprocal_tail_high_log_weight_sum_zero_remove c] at h
  have hleft :
      (∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊,
        (Real.log (d : ℝ) ^ 2)⁻¹ * (c d * Real.log (d : ℝ) ^ 2)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) - ∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d := by
    rw [← reciprocal_tail_high_log_weight_sum_Ioc_difference c _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro d hd
    have hda : a < (d : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ a)).mp (Finset.mem_Ioc.mp hd).1
    have hl : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (lt_trans ha hda)).ne'
    field_simp
  rw [hleft] at h
  have hint :
      (∫ t in Set.Ioc a x, deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t *
        ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) =
      -(2 * ∫ t in a..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
          (t * Real.log t ^ 3)) := by
    rw [← intervalIntegral.integral_of_le hax]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    dsimp only
    rw [hdv t ht]
    ring
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm ((Real.log _) ^ 2)⁻¹] at h ⊢
  linarith

lemma reciprocal_tail_high_log_squared_weight_removal_bound (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d
  let W : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1]) (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hrem : |∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    calc
      _ ≤ ∫ t in a..x, |W t / (t * Real.log t ^ 3)| :=
        intervalIntegral.abs_integral_le_integral_abs hax
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hax] at ht
        dsimp only
        rw [abs_div, abs_of_pos (hden t ht)]
  have hid := reciprocal_tail_high_log_squared_weight_removal_identity c a x ha hax
  change M x = (M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2 +
    2 * ∫ t in a..x, W t / (t * Real.log t ^ 3) at hid
  change |M x| ≤ |M a - W a / Real.log a ^ 2| + |W x| / Real.log x ^ 2 +
    2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3)
  rw [hid]
  have h1 := abs_add_le (M a - W a / Real.log a ^ 2) (W x / Real.log x ^ 2)
  have h2 := abs_add_le ((M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2)
    (2 * ∫ t in a..x, W t / (t * Real.log t ^ 3))
  have hW : |W x / Real.log x ^ 2| = |W x| / Real.log x ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos (Real.log_pos (lt_of_lt_of_le ha hax)) 2)]
  have h3 : |2 * ∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hrem (by norm_num)
  rw [hW] at h1
  linarith

theorem reciprocal_tail_high_log_squared_weight_removal_certificate (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  exact ⟨reciprocal_tail_high_log_weight_kernel_intervalIntegrable c a x ha hax,
    reciprocal_tail_high_log_squared_weight_removal_identity c a x ha hax,
    reciprocal_tail_high_log_squared_weight_removal_bound c a x ha hax⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_hasDerivAt_log_weight_majorant (α t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => α * u / Real.log u ^ 2)
      (α * (Real.log t - 2) / Real.log t ^ 3) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((hasDerivAt_id t).const_mul α).div
    ((Real.hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl0)
  convert hd using 1 <;>
    (try simp only [Pi.div_apply, Pi.pow_apply, id_eq, mul_one, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]) <;>
    first | rfl | (field_simp [hl0, ht0] <;> ring)

lemma reciprocal_tail_high_log_weight_envelope_integral_bound (α β a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hβα : 2 * α ≤ β) :
    (∫ t in a..x, (α * Real.log t - β) / Real.log t ^ 3) ≤
      α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2 := by
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by
      change t ≠ 0
      linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht
    exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hcont : ContinuousOn (fun t : ℝ =>
      (α * Real.log t - β) / Real.log t ^ 3) (Set.Icc a x) :=
    ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (hl0 t ht))
  have hdcont : ContinuousOn (fun t : ℝ =>
      α * (Real.log t - 2) / Real.log t ^ 3) (Set.Icc a x) :=
    (continuousOn_const.mul (hl.sub continuousOn_const)).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (hl0 t ht))
  have hdi : IntervalIntegrable (fun t : ℝ =>
      α * (Real.log t - 2) / Real.log t ^ 3) volume a x :=
    hdcont.intervalIntegrable_of_Icc hax
  have hderiv : ∀ t ∈ Set.uIcc a x,
      HasDerivAt (fun u : ℝ => α * u / Real.log u ^ 2)
        (α * (Real.log t - 2) / Real.log t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    exact reciprocal_tail_high_hasDerivAt_log_weight_majorant α t (lt_of_lt_of_le ha ht.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdi
  rw [← hi]
  apply intervalIntegral.integral_mono_on hax (hcont.intervalIntegrable_of_Icc hax) hdi
  intro t ht
  apply (div_le_div_iff_of_pos_right
    (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)).mpr
  nlinarith

theorem reciprocal_tail_high_log_squared_weight_removal_quantitative (c : ℕ → ℝ) (α β a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hβα : 2 * α ≤ β)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          2 * α * a / Real.log a ^ 2)
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * (α * Real.log t - β)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 := by
  let W : ℝ → ℝ := fun t => ∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1])
      (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hcont : ContinuousOn (fun t : ℝ =>
      (α * Real.log t - β) / Real.log t ^ 3) (Set.Icc a x) := by
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => by
        change t ≠ 0
        linarith [ht.1])
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne')
  have habs : IntervalIntegrable (fun t : ℝ =>
      |W t| / (t * Real.log t ^ 3)) volume a x := by
    apply (intervalIntegrable_congr (g := fun t : ℝ =>
      |W t / (t * Real.log t ^ 3)|) ?_).mpr
    · exact (reciprocal_tail_high_log_weight_kernel_intervalIntegrable c a x ha hax).abs
    · intro t ht
      have ht' : t ∈ Set.Icc a x := by
        rw [Set.uIoc_of_le hax] at ht
        exact ⟨ht.1.le, ht.2⟩
      change |W t| / (t * Real.log t ^ 3) = |W t / (t * Real.log t ^ 3)|
      rw [abs_div, abs_of_pos (hden t ht')]
  have himono : (∫ t in a..x, |W t| / (t * Real.log t ^ 3)) ≤
      ∫ t in a..x, (α * Real.log t - β) / Real.log t ^ 3 := by
    apply intervalIntegral.integral_mono_on hax habs
      (hcont.intervalIntegrable_of_Icc hax)
    intro t ht
    calc
      _ ≤ (t * (α * Real.log t - β)) / (t * Real.log t ^ 3) :=
        div_le_div_of_nonneg_right (hW t ht) (hden t ht).le
      _ = _ := by
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
  have hi := himono.trans (reciprocal_tail_high_log_weight_envelope_integral_bound α β a x ha hax hβα)
  have hWx : |W x| / Real.log x ^ 2 ≤
      x * (α * Real.log x - β) / Real.log x ^ 2 :=
    div_le_div_of_nonneg_right (hW x ⟨hax, le_rfl⟩) (sq_nonneg _)
  have hb := reciprocal_tail_high_log_squared_weight_removal_bound c a x ha hax
  change |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
    |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) - W a / Real.log a ^ 2| +
      |W x| / Real.log x ^ 2 +
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) at hb
  have hcancel :
      2 * α * a / Real.log a ^ 2 + x * (α * Real.log x - β) / Real.log x ^ 2 +
        2 * (α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2) =
          x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 := by ring
  rw [← hcancel]
  dsimp only [W] at *
  linarith

theorem reciprocal_tail_high_summatory_explicit_log_decay_of_log_squared (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          13 * a / (500 * Real.log a ^ 2))
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * ((13 / 1000 : ℝ) * Real.log t - 18 / 125)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * ((13 / 1000 : ℝ) * Real.log x - 59 / 500) / Real.log x ^ 2 := by
  have hbase :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          2 * (13 / 1000 : ℝ) * a / Real.log a ^ 2 := by
    convert hstart using 1 <;> ring
  have h := reciprocal_tail_high_log_squared_weight_removal_quantitative c (13 / 1000) (18 / 125)
    a x ha hax (by norm_num) hbase hW
  convert h using 1 <;> ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma reciprocal_tail_high_log_weight_absolute_kernel_majorant (c : ℕ → ℝ) (α β a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hβα : 2 * α ≤ β)
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * (α * Real.log t - β)) :
    (∫ t in a..x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| / (t * Real.log t ^ 3)) ≤
      α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2 := by
  let W : ℝ → ℝ := fun t => ∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1])
      (pow_pos (Real.log_pos (ha.trans_le ht.1)) 3)
  have hcont : ContinuousOn (fun t : ℝ =>
      (α * Real.log t - β) / Real.log t ^ 3) (Set.Icc a x) := by
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 3)
      (fun t ht => pow_ne_zero 3 (Real.log_pos (ha.trans_le ht.1)).ne')
  have habs : IntervalIntegrable (fun t : ℝ =>
      |W t| / (t * Real.log t ^ 3)) volume a x := by
    apply (intervalIntegrable_congr (g := fun t : ℝ =>
      |W t / (t * Real.log t ^ 3)|) ?_).mpr
    · exact (reciprocal_tail_high_log_weight_kernel_intervalIntegrable c a x ha hax).abs
    · intro t ht
      have ht' : t ∈ Set.Icc a x := by
        rw [Set.uIoc_of_le hax] at ht
        exact ⟨ht.1.le, ht.2⟩
      change |W t| / (t * Real.log t ^ 3) = |W t / (t * Real.log t ^ 3)|
      rw [abs_div, abs_of_pos (hden t ht')]
  have himono : (∫ t in a..x, |W t| / (t * Real.log t ^ 3)) ≤
      ∫ t in a..x, (α * Real.log t - β) / Real.log t ^ 3 := by
    apply intervalIntegral.integral_mono_on hax habs
      (hcont.intervalIntegrable_of_Icc hax)
    intro t ht
    calc
      _ ≤ (t * (α * Real.log t - β)) / (t * Real.log t ^ 3) :=
        div_le_div_of_nonneg_right (hW t ht) (hden t ht).le
      _ = _ := by
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
  exact himono.trans (reciprocal_tail_high_log_weight_envelope_integral_bound α β a x ha hax hβα)

theorem reciprocal_tail_high_log_squared_weight_removal_coarse_anchor (c : ℕ → ℝ) (α β a x L : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hL : 0 < L) (hβα : 2 * α ≤ β)
    (hanchor : |∑ n ∈ Icc 1 ⌊a⌋₊, c n| ≤ a / L)
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * (α * Real.log t - β)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 +
        a / L + a * (α * Real.log a - β - 2 * α) / Real.log a ^ 2 := by
  let W : ℝ → ℝ := fun t => ∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hstart : |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) - W a / Real.log a ^ 2| ≤
      a / L + a * (α * Real.log a - β) / Real.log a ^ 2 := by
    calc
      _ ≤ |∑ n ∈ Icc 1 ⌊a⌋₊, c n| + |W a / Real.log a ^ 2| := abs_sub _ _
      _ = |∑ n ∈ Icc 1 ⌊a⌋₊, c n| + |W a| / Real.log a ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg (Real.log a))]
      _ ≤ _ := by
        have hh := div_le_div_of_nonneg_right (hW a ⟨le_rfl, hax⟩) (sq_nonneg (Real.log a))
        change |W a| / Real.log a ^ 2 ≤ _ at hh
        linarith
  have hxW := div_le_div_of_nonneg_right (hW x ⟨hax, le_rfl⟩) (sq_nonneg (Real.log x))
  have hi := reciprocal_tail_high_log_weight_absolute_kernel_majorant c α β a x ha hax hβα hW
  have hb := reciprocal_tail_high_log_squared_weight_removal_bound c a x ha hax
  change |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
    |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) - W a / Real.log a ^ 2| +
      |W x| / Real.log x ^ 2 +
      2 * (∫ t in a..x, |W t| / (t * Real.log t ^ 3)) at hb
  have heq : a / L + a * (α * Real.log a - β) / Real.log a ^ 2 +
      x * (α * Real.log x - β) / Real.log x ^ 2 +
      2 * (α * x / Real.log x ^ 2 - α * a / Real.log a ^ 2) =
      x * (α * Real.log x - (β - 2 * α)) / Real.log x ^ 2 +
        a / L + a * (α * Real.log a - β - 2 * α) / Real.log a ^ 2 := by ring
  rw [← heq]
  dsimp only [W] at *
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma reciprocal_tail_high_corrected_tail_anchor_log_bounds :
    (621 / 10 : ℝ) ≤ Real.log 1000000000000000000000000000 ∧
      Real.log (1000000000000000000000000000 : ℝ) ≤ 311 / 5 := by
  have hlogten : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [show (1000000000000000000000000000 : ℝ) = 10 ^ (27 : ℕ) by norm_num,
    Real.log_pow, hlogten]
  norm_num only [Nat.cast_ofNat]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma reciprocal_tail_high_corrected_tail_anchor_error_absorbed (x : ℝ)
    (hx : 10000000000000000000000000000 ≤ x) :
    (1000000000000000000000000000 : ℝ) / 2500 ≤
      (101 / 500) * x / Real.log x ^ 2 := by
  let T : ℝ := 10000000000000000000000000000
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hxe : Real.exp 2 ≤ T := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith
  have hTx : T ≤ x := hx
  have hlogT : Real.log T ≤ 65 := by
    have hlogten : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [show T = (10 : ℝ) ^ (28 : ℕ) by norm_num [T], Real.log_pow, hlogten]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hs := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hs
  have hsquare' : Real.log x ^ 2 / x ≤ 65 ^ 2 / T :=
    hsquare.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogT0 hlogT 2) hTpos.le)
  have hprod : ((1000000000000000000000000000 : ℝ) / 2500) *
      (Real.log x ^ 2 / x) ≤ 101 / 500 := by
    calc
      _ ≤ ((1000000000000000000000000000 : ℝ) / 2500) * (65 ^ 2 / T) :=
        mul_le_mul_of_nonneg_left hsquare' (by norm_num)
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ (sq_pos_of_pos hlogxp)).mpr
  rw [← mul_div_assoc] at hprod
  have h := (div_le_iff₀ hxpos).mp hprod
  convert h using 1 <;> first | rfl | ring

theorem reciprocal_tail_high_moebius_summatory_point_zero_one_four_of_tail_log_squared
    (x : ℝ) (hx : 10000000000000000000000000000 ≤ x)
    (hanchor : |∑ n ∈ Icc 1 1000000000000000000000000000,
      ((moebius n : ℤ) : ℝ)| ≤ (1000000000000000000000000000 : ℝ) / 4345)
    (hW : ∀ N : ℕ, 1000000000000000000000000000 ≤ N →
      |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
        (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ)| ≤
      (7 / 500) * x / Real.log x := by
  let a : ℝ := 1000000000000000000000000000
  have ha : 1 < a := by norm_num [a]
  have hax : a ≤ x := by dsimp only [a]; linarith
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogalo : (621 / 10 : ℝ) ≤ Real.log a := reciprocal_tail_high_corrected_tail_anchor_log_bounds.1
  have hlogahi : Real.log a ≤ (311 / 5 : ℝ) := reciprocal_tail_high_corrected_tail_anchor_log_bounds.2
  have hrealW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
        t * ((7 / 500) * Real.log t - 23 / 100) := by
    intro t ht
    have hlo : 1000000000000000000000000000 ≤ ⌊t⌋₊ := Nat.le_floor ht.1
    have hNt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith [ht.1])
    have hNpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
    have hNlo : a ≤ (⌊t⌋₊ : ℝ) := by
      dsimp only [a]
      exact_mod_cast hlo
    have hlogNlo : (621 / 10 : ℝ) ≤ Real.log (⌊t⌋₊ : ℝ) :=
      hlogalo.trans (Real.log_le_log (by linarith) hNlo)
    have hlogNt := Real.log_le_log hNpos hNt
    have hc0 : 0 ≤ (7 / 500) * Real.log (⌊t⌋₊ : ℝ) - 23 / 100 := by nlinarith
    have hct : 0 ≤ (7 / 500) * Real.log t - 23 / 100 := by nlinarith
    calc
      _ ≤ (⌊t⌋₊ : ℝ) * ((7 / 500) * Real.log (⌊t⌋₊ : ℝ) - 23 / 100) := hW _ hlo
      _ ≤ (⌊t⌋₊ : ℝ) * ((7 / 500) * Real.log t - 23 / 100) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hNpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hNt hct
  have hanchorr : |∑ n ∈ Icc 1 ⌊a⌋₊, ((moebius n : ℤ) : ℝ)| ≤ a / 4345 := by
    simpa only [a, Nat.floor_ofNat] using hanchor
  have hb := reciprocal_tail_high_log_squared_weight_removal_coarse_anchor
    (fun n => ((moebius n : ℤ) : ℝ)) (7 / 500) (23 / 100) a x 4345
    ha hax (by norm_num) (by norm_num) hanchorr hrealW
  have hcoef : (1 / 4345 : ℝ) +
      ((7 / 500) * Real.log a - 23 / 100 - 2 * (7 / 500)) / Real.log a ^ 2 ≤ 1 / 2500 := by
    have hh : ((7 / 500) * Real.log a - 23 / 100 - 2 * (7 / 500)) / Real.log a ^ 2 ≤
        (1 / 2500 : ℝ) - 1 / 4345 := by
      apply (div_le_iff₀ (sq_pos_of_pos hloga)).mpr
      have hs : (621 / 10 : ℝ) ^ 2 ≤ Real.log a ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hlogalo 2
      have hm := mul_le_mul_of_nonneg_left hs
        (by norm_num : (0 : ℝ) ≤ 1 / 2500 - 1 / 4345)
      nlinarith
    linarith
  have hD : a / 4345 + a * ((7 / 500) * Real.log a - 23 / 100 - 2 * (7 / 500)) /
      Real.log a ^ 2 ≤ a / 2500 := by
    have hm := mul_le_mul_of_nonneg_left hcoef (by linarith : 0 ≤ a)
    convert hm using 1 <;> first | rfl | ring
  have habs := reciprocal_tail_high_corrected_tail_anchor_error_absorbed x hx
  change a / 2500 ≤ (101 / 500) * x / Real.log x ^ 2 at habs
  have he : x * ((7 / 500) * Real.log x - (23 / 100 - 2 * (7 / 500))) / Real.log x ^ 2 +
      (101 / 500) * x / Real.log x ^ 2 = (7 / 500) * x / Real.log x := by
    field_simp [hlogxp.ne'] <;> ring
  rw [← he]
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem reciprocal_tail_high_moebius_summatory_high_of_prime_errors_and_tail_mertens
    (x C : ℝ) (hx : 10000000000000000000000000000 ≤ x) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (hM : ∀ u : ℕ, 10000000000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ)| ≤
      (7 / 500) * x / Real.log x := by
  have hW : ∀ N : ℕ, 1000000000000000000000000000 ≤ N →
      |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
        (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := by
    intro N hN
    apply reciprocal_tail_high_moebius_log_squared_corrected_high_of_tail_mertens N C hN hC
    · intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
      have hmul : d * 10000000000000000 ≤ N :=
        (Nat.le_div_iff_mul_le (by norm_num)).mp (mem_Icc.mp hd).2
      have hmulr : (10000000000000000 : ℝ) * (d : ℝ) ≤ N := by
        exact_mod_cast (show 10000000000000000 * d ≤ N by simpa only [mul_comm] using hmul)
      have hq : (10000000000000000 : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
        (le_div_iff₀ hdr).mpr hmulr
      have hb := hRhigh ((N : ℝ) / (d : ℝ)) hq
      simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using hb
    · intro d hd
      have hd0 : 0 < d := by have := (mem_Ioc.mp hd).1; omega
      have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
      have hmul : d * 21000000000 ≤ N :=
        (Nat.le_div_iff_mul_le (by norm_num)).mp (mem_Ioc.mp hd).2
      have hmulr : (21000000000 : ℝ) * (d : ℝ) ≤ N := by
        exact_mod_cast (show 21000000000 * d ≤ N by simpa only [mul_comm] using hmul)
      have hqlo : (21000000000 : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
        (le_div_iff₀ hdr).mpr hmulr
      have hhi : N < d * 10000000000000000 :=
        (Nat.div_lt_iff_lt_mul (by norm_num)).mp (mem_Ioc.mp hd).1
      have hhir : (N : ℝ) < (10000000000000000 : ℝ) * (d : ℝ) := by
        exact_mod_cast (show N < 10000000000000000 * d by simpa only [mul_comm] using hhi)
      have hqhi : (N : ℝ) / (d : ℝ) < (10000000000000000 : ℝ) :=
        (div_lt_iff₀ hdr).mpr hhir
      have hb := hRmiddle ((N : ℝ) / (d : ℝ)) hqlo hqhi
      simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using hb
    · exact hM
  exact reciprocal_tail_high_moebius_summatory_point_zero_one_four_of_tail_log_squared x hx
    (hM 1000000000000000000000000000 (by norm_num)) hW

end Helfgott
end

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem reciprocal_tail_high_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma reciprocal_tail_high_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma reciprocal_tail_high_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem reciprocal_tail_high_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,reciprocal_tail_high_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [reciprocal_tail_high_floorRoot_two_eq_one_iff_squarefree n hn]

lemma reciprocal_tail_high_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,reciprocal_tail_high_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem reciprocal_tail_high_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast reciprocal_tail_high_coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast reciprocal_tail_high_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem reciprocal_tail_high_moebius_real_logarithmic_kernel_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d∈Finset.Icc 1 (Nat.floor x),∑ k∈Finset.Icc 1 ((Nat.floor x)/d),
      ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x := by
  let N := Nat.floor x
  have hN : 1 ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  change (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
    ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ))) = Real.log x
  have hr := reciprocal_tail_high_finite_positive_divisor_reindex N
    (fun d k => ((moebius d : ℤ) : ℝ)*Real.log (x/((d*k : ℕ) : ℝ)))
  have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (∑ d∈n.divisors,((moebius d : ℤ) : ℝ)*Real.log (x/((d*(n/d) : ℕ) : ℝ))) =
        (if n=1 then (1:ℝ) else 0)*Real.log (x/(n : ℝ)) := by
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1;omega
    have hemul : ∀ d∈n.divisors,d*(n/d)=n := fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [Finset.sum_congr rfl (fun d hd => by rw [hemul d hd]),←Finset.sum_mul]
    have hm : (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then 1 else 0 := by
      exact_mod_cast reciprocal_tail_high_moebius_divisor_sum n hn0
    rw [hm]
  rw [←hr,Finset.sum_congr rfl he]
  simp [Finset.mem_Icc,hN]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_reciprocal_rectangle_intervalIntegrable (a b l r : ℝ) (ha : 0 < a) :
    IntervalIntegrable (fun t : ℝ => if a ≤ t ∧ t ≤ b then t⁻¹ else 0)
      volume l r := by
  have hm : Measurable (fun t : ℝ => if a ≤ t ∧ t ≤ b then t⁻¹ else 0) :=
    Measurable.ite (measurableSet_Ici.inter measurableSet_Iic)
      measurable_id.inv measurable_const
  apply (intervalIntegrable_const (c := a⁻¹)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  split_ifs with ht
  · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha.trans_le ht.1))]
    exact (inv_le_inv₀ (ha.trans_le ht.1) ha).mpr ht.1
  · simp only [norm_zero]
    exact (inv_pos.mpr ha).le

lemma reciprocal_tail_high_reciprocal_rectangle_integral (x a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ x) :
    (∫ t in (1 : ℝ)..x, if a ≤ t ∧ t ≤ b then t⁻¹ else 0) =
      Real.log (b / a) := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  let f : ℝ → ℝ := fun t => if a ≤ t ∧ t ≤ b then t⁻¹ else 0
  have hi (l r : ℝ) : IntervalIntegrable f volume l r :=
    reciprocal_tail_high_reciprocal_rectangle_intervalIntegrable a b l r hap
  have hleft : (∫ t in (1 : ℝ)..a, f t) = 0 := by
    calc
      _ = ∫ _ in (1 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha
        intro t ht
        exact if_neg (by intro h; linarith [ht.2, h.1])
      _ = 0 := by simp
  have hmid : (∫ t in a..b, f t) = Real.log (b / a) := by
    calc
      _ = ∫ t in a..b, t⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        exact if_pos ⟨ht.1.le, ht.2.le⟩
      _ = _ := integral_inv_of_pos hap hbp
  have hright : (∫ t in b..x, f t) = 0 := by
    calc
      _ = ∫ _ in b..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb
        intro t ht
        exact if_neg (by intro h; linarith [ht.1, h.2])
      _ = 0 := by simp
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals (hi 1 a) (hi a b)
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals (hi 1 b) (hi b x)
  rw [hleft, hmid, zero_add] at hsplit₁
  rw [← hsplit₁, hright, add_zero] at hsplit₂
  exact hsplit₂.symm

lemma reciprocal_tail_high_sum_Icc_floor_cutoff (c : ℕ → ℝ) (x t : ℝ) (ht : 0 ≤ t) (htx : t ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, if (d : ℝ) ≤ t then c d else 0) =
      ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d := by
  have hsub : Finset.Icc 1 ⌊t⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htx)
  have he := Finset.sum_subset hsub (f := fun (d : ℕ) => if (d : ℝ) ≤ t then c d else 0)
    (by
      intro d hd hdt
      have hnot : ¬ (d : ℝ) ≤ t := by
        intro h
        exact hdt (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          (Nat.le_floor_iff ht).mpr h⟩)
      exact if_neg hnot)
  rw [← he]
  apply Finset.sum_congr rfl
  intro d hd
  exact if_pos ((Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hd).2)

lemma reciprocal_tail_high_floor_div_as_finite_cutoffs (x t : ℝ) (hx : 1 ≤ x) (ht : 1 ≤ t) :
    (⌊x / t⌋₊ : ℝ) =
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if t ≤ x / (k : ℝ) then (1 : ℝ) else 0 := by
  have hxp : 0 < x := by linarith
  have htp : 0 < t := by linarith
  have hxt : x / t ≤ x := (div_le_iff₀ htp).mpr (by nlinarith)
  have he := reciprocal_tail_high_sum_Icc_floor_cutoff (fun _ => (1 : ℝ)) x (x / t)
    (div_nonneg hxp.le htp.le) hxt
  have hswap :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if (k : ℝ) ≤ x / t then (1 : ℝ) else 0) =
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if t ≤ x / (k : ℝ) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hiff : (k : ℝ) ≤ x / t ↔ t ≤ x / (k : ℝ) := by
      rw [le_div_iff₀ htp, le_div_iff₀ hkp, mul_comm (k : ℝ) t]
    simp only [hiff]
  rw [hswap] at he
  simpa using he.symm

lemma reciprocal_tail_high_moebius_floor_kernel_as_rectangles (x t : ℝ) (hx : 1 ≤ x)
    (ht : t ∈ Set.Icc 1 x) :
    (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
  rw [reciprocal_tail_high_floor_div_as_finite_cutoffs x t hx ht.1,
    ← reciprocal_tail_high_sum_Icc_floor_cutoff (fun d => ((moebius d : ℤ) : ℝ)) x t
      (by linarith [ht.1]) ht.2]
  rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp_all

lemma reciprocal_tail_high_moebius_floor_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x := by
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_tail_high_reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
  have hs : IntervalIntegrable (fun t : ℝ =>
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    convert IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊) (fun d hd =>
      IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊) (fun k _ => hterm d hd k)) using 1 <;>
      first | rfl | (funext t; simp only [Finset.sum_apply])
  apply hs.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  exact (reciprocal_tail_high_moebius_floor_kernel_as_rectangles x t hx ⟨ht.1.le, ht.2.le⟩).symm

theorem reciprocal_tail_high_moebius_logarithmic_floor_integral (x : ℝ) (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) (k : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    exact (reciprocal_tail_high_reciprocal_rectangle_intervalIntegrable d (x / k) 1 x hdp).const_mul _
  have hrow (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊) :
      IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) volume 1 x := by
    convert IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊)
      (fun k _ => hterm d hd k) using 1 <;>
      first | rfl | (funext t; simp only [Finset.sum_apply])
  have heach (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊x⌋₊)
      (k : ℕ) (hk : k ∈ Finset.Icc 1 ⌊x⌋₊) :
      (∫ t in (1 : ℝ)..x, ((moebius d : ℤ) : ℝ) *
        (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0)) =
        if k ≤ ⌊x⌋₊ / d then ((moebius d : ℤ) : ℝ) *
          Real.log (x / ((d * k : ℕ) : ℝ)) else 0 := by
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd1
    have hkp : (0 : ℝ) < k := by exact_mod_cast hk1
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rw [intervalIntegral.integral_const_mul]
    by_cases hkd : k ≤ ⌊x⌋₊ / d
    · rw [if_pos hkd]
      have hprod : d * k ≤ ⌊x⌋₊ := by
        calc
          _ ≤ d * (⌊x⌋₊ / d) := Nat.mul_le_mul_left d hkd
          _ ≤ ⌊x⌋₊ := by simpa only [mul_comm] using Nat.div_mul_le_self ⌊x⌋₊ d
      have hprodR : (d : ℝ) * k ≤ x := by
        have h := (Nat.le_floor_iff hx0).mp hprod
        simpa only [Nat.cast_mul] using h
      have hdxk : (d : ℝ) ≤ x / k := (le_div_iff₀ hkp).mpr hprodR
      have hxkx : x / (k : ℝ) ≤ x := (div_le_iff₀ hkp).mpr (by nlinarith)
      rw [reciprocal_tail_high_reciprocal_rectangle_integral x d (x / k) hdR hdxk hxkx]
      congr 2
      push_cast
      field_simp
    · rw [if_neg hkd]
      have hnot : ¬ (d : ℝ) ≤ x / k := by
        intro h
        have hprodR : (k : ℝ) * d ≤ x := by
          have hh := (le_div_iff₀ hkp).mp h
          nlinarith
        have hprodN : k * d ≤ ⌊x⌋₊ :=
          (Nat.le_floor_iff hx0).mpr (by simpa only [Nat.cast_mul] using hprodR)
        exact hkd ((Nat.le_div_iff_mul_le hd1).mpr hprodN)
      have hz : (fun t : ℝ => if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) =
          (fun _ : ℝ => (0 : ℝ)) := by
        funext t
        exact if_neg (fun h => hnot (h.1.trans h.2))
      rw [hz]
      simp
  calc
    _ = ∫ t in (1 : ℝ)..x,
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          ((moebius d : ℤ) : ℝ) *
            (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact reciprocal_tail_high_moebius_floor_kernel_as_rectangles x t hx ht
    _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ∫ t in (1 : ℝ)..x, ((moebius d : ℤ) : ℝ) *
          (if (d : ℝ) ≤ t ∧ t ≤ x / (k : ℝ) then t⁻¹ else 0) := by
      rw [intervalIntegral.integral_finsetSum hrow]
      apply Finset.sum_congr rfl
      intro d hd
      exact intervalIntegral.integral_finsetSum (fun k _ => hterm d hd k)
    _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ / d),
        ((moebius d : ℤ) : ℝ) * Real.log (x / ((d * k : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_congr rfl (fun k hk => heach d hd k hk)]
      have hsub : Finset.Icc 1 (⌊x⌋₊ / d) ⊆ Finset.Icc 1 ⌊x⌋₊ :=
        Finset.Icc_subset_Icc le_rfl (Nat.div_le_self _ _)
      rw [← Finset.sum_subset hsub (f := fun k : ℕ =>
        if k ≤ ⌊x⌋₊ / d then ((moebius d : ℤ) : ℝ) *
          Real.log (x / ((d * k : ℕ) : ℝ)) else 0) (by
            intro k hk hnot
            exact if_neg (fun h => hnot (Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp hk).1, h⟩)))]
      apply Finset.sum_congr rfl
      intro k hk
      exact if_pos (Finset.mem_Icc.mp hk).2
    _ = Real.log x := reciprocal_tail_high_moebius_real_logarithmic_kernel_identity x hx

theorem reciprocal_tail_high_moebius_logarithmic_floor_integral_certificate (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x ∧
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by
  exact ⟨reciprocal_tail_high_moebius_floor_kernel_intervalIntegrable x hx, reciprocal_tail_high_moebius_logarithmic_floor_integral x hx⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_sum_Icc_zero_remove (c : ℕ → ℝ) (hc : c 0 = 0) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d) = ∑ d ∈ Finset.Icc 1 N, c d := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [hc, zero_add]
  rfl

lemma reciprocal_tail_high_summatory_mul_continuous_intervalIntegrable (c : ℕ → ℝ) (f : ℝ → ℝ)
    (x : ℝ) (hx : 1 ≤ x) (hf : ContinuousOn f (Set.Icc 1 x)) :
    IntervalIntegrable (fun t : ℝ => f t * ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d)
      volume 1 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 1)
    (hf.integrableOn_Icc)

lemma reciprocal_tail_high_moebius_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hi := reciprocal_tail_high_summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => t⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

lemma reciprocal_tail_high_moebius_summatory_div_sq_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) volume 1 x := by
  have hf : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 1 x) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have hi := reciprocal_tail_high_summatory_mul_continuous_intervalIntegrable
    (fun d => ((moebius d : ℤ) : ℝ)) (fun t : ℝ => (t ^ 2)⁻¹) x hx hf
  simpa only [div_eq_mul_inv, mul_comm] using hi

theorem reciprocal_tail_high_moebius_reciprocal_abel_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        ∫ t in (1 : ℝ)..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) :=
    ((continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 1 x) := by
    simpa only [deriv_inv'] using hc.integrableOn_Icc
  have hmu0 : ((moebius 0 : ℤ) : ℝ) = 0 := by simp
  have h := sum_mul_eq_sub_integral_mul₀ (fun d => ((moebius d : ℤ) : ℝ))
    hmu0 x hd hi
  simp_rw [reciprocal_tail_high_sum_Icc_zero_remove (fun d => ((moebius d : ℤ) : ℝ)) hmu0] at h
  have hleft :
      (∑ d ∈ Finset.Icc 0 ⌊x⌋₊, (d : ℝ)⁻¹ * ((moebius d : ℤ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [reciprocal_tail_high_sum_Icc_zero_remove _ (by simp)]
    apply Finset.sum_congr rfl
    intro d _
    simp only [div_eq_mul_inv, mul_comm]
  rw [hleft] at h
  have hneg :
      (∫ t in Set.Ioc (1 : ℝ) x,
        deriv (fun t : ℝ => t⁻¹) t * ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) =
        -(∫ t in (1 : ℝ)..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    simp_rw [deriv_inv, neg_mul, mul_comm ((_)⁻¹), ← div_eq_mul_inv]
    exact intervalIntegral.integral_neg
  rw [hneg] at h
  simpa only [div_eq_mul_inv, mul_comm, sub_neg_eq_add] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_moebius_fractional_kernel_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (x / t - (⌊x / t⌋₊ : ℝ)) *
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) volume 1 x := by
  have hi := ((reciprocal_tail_high_moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x).sub
    (reciprocal_tail_high_moebius_floor_kernel_intervalIntegrable x hx)
  apply hi.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htne : t ≠ 0 := by linarith [ht.1]
  dsimp only
  field_simp [htne]

theorem reciprocal_tail_high_moebius_reciprocal_fractional_identity (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        (∫ t in (1 : ℝ)..x, (x / t - (⌊x / t⌋₊ : ℝ)) *
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) / x +
        Real.log x / x := by
  have hxne : x ≠ 0 := by linarith
  have he :
      (∫ t in (1 : ℝ)..x, (x / t - (⌊x / t⌋₊ : ℝ)) *
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      x * (∫ t in (1 : ℝ)..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) - Real.log x := by
    calc
      _ = ∫ t in (1 : ℝ)..x,
          x * ((∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t ^ 2) -
            (⌊x / t⌋₊ : ℝ) *
              (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have htne : t ≠ 0 := by linarith [ht.1]
        field_simp [htne]
      _ = _ := by
        rw [intervalIntegral.integral_sub
          ((reciprocal_tail_high_moebius_summatory_div_sq_intervalIntegrable x hx).const_mul x)
          (reciprocal_tail_high_moebius_floor_kernel_intervalIntegrable x hx),
          intervalIntegral.integral_const_mul, reciprocal_tail_high_moebius_logarithmic_floor_integral x hx]
  rw [reciprocal_tail_high_moebius_reciprocal_abel_identity x hx, he]
  field_simp
  ring

lemma reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) volume 1 x := by
  apply (reciprocal_tail_high_moebius_summatory_div_intervalIntegrable x hx).abs.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le hx] at ht
  have htp : 0 < t := by linarith [ht.1]
  exact abs_div _ t |>.trans (by rw [abs_of_pos htp])

theorem reciprocal_tail_high_moebius_reciprocal_el_marraki_bound (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        (∫ t in (1 : ℝ)..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) / x +
        Real.log x / x := by
  have hxp : 0 < x := by linarith
  let R : ℝ → ℝ := fun t => (x / t - (⌊x / t⌋₊ : ℝ)) *
    (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t
  have hiR : IntervalIntegrable R volume 1 x :=
    reciprocal_tail_high_moebius_fractional_kernel_intervalIntegrable x hx
  have hiB := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable x hx
  have hrem : |∫ t in (1 : ℝ)..x, R t| ≤
      ∫ t in (1 : ℝ)..x, |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t := by
    apply (intervalIntegral.abs_integral_le_integral_abs hx).trans
    apply intervalIntegral.integral_mono_on hx hiR.abs hiB
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hyt : 0 ≤ x / t := div_nonneg hxp.le htp.le
    have hlo : 0 ≤ x / t - (⌊x / t⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hyt)
    have hup : x / t - (⌊x / t⌋₊ : ℝ) ≤ 1 := by
      have hh := Nat.lt_floor_add_one (x / t)
      linarith
    dsimp only [R]
    rw [abs_div, abs_mul, abs_of_nonneg hlo, abs_of_pos htp]
    apply div_le_div_of_nonneg_right _ htp.le
    calc
      _ ≤ 1 * |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_right hup (abs_nonneg _)
      _ = _ := one_mul _
  have hid := reciprocal_tail_high_moebius_reciprocal_fractional_identity x hx
  change (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
      (∫ t in (1 : ℝ)..x, R t) / x + Real.log x / x at hid
  rw [hid]
  calc
    _ ≤ |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x +
        (∫ t in (1 : ℝ)..x, R t) / x| + |Real.log x / x| := abs_add_le _ _
    _ ≤ (|(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x| +
        |(∫ t in (1 : ℝ)..x, R t) / x|) + |Real.log x / x| :=
      by
        have hh := abs_add_le
          ((∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)) / x)
          ((∫ t in (1 : ℝ)..x, R t) / x)
        linarith
    _ = |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        |∫ t in (1 : ℝ)..x, R t| / x + Real.log x / x := by
      rw [abs_div, abs_div, abs_div, abs_of_pos hxp,
        abs_of_nonneg (Real.log_nonneg hx)]
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hrem hxp.le
      linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma reciprocal_tail_high_hasDerivAt_scaled_id_div_log (A t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => A * t / Real.log t)
      ((A * Real.log t - A) / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((hasDerivAt_id t).const_mul A).div (Real.hasDerivAt_log ht0) hl0
  convert hd using 1 <;> first | rfl | (dsimp only [id]; field_simp [ht0])

lemma reciprocal_tail_high_scaled_log_primitive_integral (A a x : ℝ) (ha : 1 < a) (hax : a ≤ x) :
    (∫ t in a..x, (A * Real.log t - A) / Real.log t ^ 2) =
      A * x / Real.log x - A * a / Real.log a := by
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hi : IntervalIntegrable (fun t : ℝ => (A * Real.log t - A) / Real.log t ^ 2)
      volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro t ht
  rw [Set.uIcc_of_le hax] at ht
  exact reciprocal_tail_high_hasDerivAt_scaled_id_div_log A t (lt_of_lt_of_le ha ht.1)

theorem reciprocal_tail_high_moebius_reciprocal_decay_transfer (a x A B C : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hBA : A ≤ B)
    (hM : ∀ t ∈ Set.Icc a x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        (A * Real.log t - B) * t / Real.log t ^ 2)
    (hinitial : (∫ t in (1 : ℝ)..a,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ C) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (2 * A * Real.log x - B) / Real.log x ^ 2 +
        (C - A * a / Real.log a + Real.log x) / x := by
  have hx : 1 ≤ x := (le_of_lt ha).trans hax
  have hxp : 0 < x := by linarith
  have hxl : Real.log x ≠ 0 := (Real.log_pos (lt_of_lt_of_le ha hax)).ne'
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)
  have hi1a := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable a ha.le
  have hi1x := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable x hx
  have hiax : IntervalIntegrable (fun t : ℝ => |M t| / t) volume a x :=
    hi1a.symm.trans hi1x
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hiP : IntervalIntegrable (fun t : ℝ => (A * Real.log t - A) / Real.log t ^ 2)
      volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  have hiupper : (∫ t in a..x, |M t| / t) ≤
      A * x / Real.log x - A * a / Real.log a := by
    rw [← reciprocal_tail_high_scaled_log_primitive_integral A a x ha hax]
    apply intervalIntegral.integral_mono_on hax hiax hiP
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    calc
      |M t| / t ≤ ((A * Real.log t - B) * t / Real.log t ^ 2) / t :=
        div_le_div_of_nonneg_right (hM t ht) htp.le
      _ = (A * Real.log t - B) / Real.log t ^ 2 := by
        field_simp
      _ ≤ (A * Real.log t - A) / Real.log t ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hitotal : (∫ t in (1 : ℝ)..x, |M t| / t) ≤
      C + A * x / Real.log x - A * a / Real.log a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1a hiax]
    change (∫ t in (1 : ℝ)..a, |M t| / t) ≤ C at hinitial
    linarith
  have hxM : |M x| / x ≤ (A * Real.log x - B) / Real.log x ^ 2 := by
    calc
      _ ≤ ((A * Real.log x - B) * x / Real.log x ^ 2) / x :=
        div_le_div_of_nonneg_right (hM x ⟨hax, le_rfl⟩) hxp.le
      _ = _ := by field_simp
  have hi := div_le_div_of_nonneg_right hitotal hxp.le
  have hel := reciprocal_tail_high_moebius_reciprocal_el_marraki_bound x hx
  change |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
    |M x| / x + (∫ t in (1 : ℝ)..x, |M t| / t) / x + Real.log x / x at hel
  have halg :
      (A * Real.log x - B) / Real.log x ^ 2 +
        (C + A * x / Real.log x - A * a / Real.log a) / x + Real.log x / x =
      (2 * A * Real.log x - B) / Real.log x ^ 2 +
        (C - A * a / Real.log a + Real.log x) / x := by
    field_simp
    ring
  rw [← halg]
  linarith

lemma reciprocal_tail_high_logarithmic_initial_error_bound (x : ℝ) (hx : 1200000 ≤ x) :
    (303 + Real.log x) / x ≤ (4 / 1000) / Real.log x := by
  let T : ℝ := 1200000
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hxe : Real.exp 2 ≤ T := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith
  have hTe : Real.exp 1 ≤ T := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hxe
  have hTx : T ≤ x := hx
  have hlogT : Real.log T ≤ 15 := by
    apply (Real.log_le_iff_le_exp hTpos).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : T ≤ ∑ i ∈ Finset.range 15, (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [T, Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hlin : Real.log x / x ≤ Real.log T / T :=
    Real.log_div_self_antitoneOn hTe (hTe.trans hTx) hTx
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hsq := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hsq
  have hlogT2 : Real.log T ^ 2 ≤ 15 ^ 2 :=
    pow_le_pow_left₀ hlogT0 hlogT 2
  have hbound : 303 * (Real.log x / x) + Real.log x ^ 2 / x ≤ 4 / 1000 := by
    calc
      _ ≤ 303 * (Real.log T / T) + Real.log T ^ 2 / T := by
        have h1 := mul_le_mul_of_nonneg_left hlin (by norm_num : (0 : ℝ) ≤ 303)
        linarith
      _ ≤ 303 * (15 / T) + 15 ^ 2 / T := by
        have h1 := div_le_div_of_nonneg_right hlogT hTpos.le
        have h2 := div_le_div_of_nonneg_right hlogT2 hTpos.le
        linarith
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ hlogxp).mpr
  convert hbound using 1 <;> first | rfl | ring

theorem reciprocal_tail_high_moebius_reciprocal_point_zero_three_of_summatory_bound (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        ((13 / 1000) * Real.log t - 118 / 1000) * t / Real.log t ^ 2)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hxa : (1078853 : ℝ) ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga : 0 < Real.log (1078853 : ℝ) := Real.log_pos (by norm_num)
  have h := reciprocal_tail_high_moebius_reciprocal_decay_transfer 1078853 x (13 / 1000) (118 / 1000) 303
    (by norm_num) hxa (by norm_num) hM hinitial
  have hmain : (2 * (13 / 1000) * Real.log x - 118 / 1000) / Real.log x ^ 2 ≤
      (26 / 1000) / Real.log x := by
    calc
      _ ≤ ((26 / 1000) * Real.log x) / Real.log x ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  have hinit : (303 - (13 / 1000) * 1078853 / Real.log (1078853 : ℝ) + Real.log x) / x ≤
      (303 + Real.log x) / x := by
    apply div_le_div_of_nonneg_right _ hxp.le
    have hp : (0 : ℝ) ≤ (13 / 1000) * 1078853 / Real.log (1078853 : ℝ) :=
      div_nonneg (by norm_num) hloga.le
    linarith
  have herr := reciprocal_tail_high_logarithmic_initial_error_bound x hx
  have heq : (26 / 1000) / Real.log x + (4 / 1000) / Real.log x =
      (3 / 100) / Real.log x := by ring
  rw [← heq]
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem reciprocal_tail_high_moebius_reciprocal_log_rate_transfer (a x A c C : ℝ)
    (ha : 1 < a) (hax : a ≤ x) (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hlog : c ≤ (c - 1) * Real.log a)
    (hM : ∀ t ∈ Set.Icc a x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤ A * t / Real.log t)
    (hinitial : (∫ t in (1 : ℝ)..a,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ C) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (1 + c) * A / Real.log x +
        (C - c * A * a / Real.log a + Real.log x) / x := by
  have hx : 1 ≤ x := ha.le.trans hax
  have hxp : 0 < x := by linarith
  have hxl : Real.log x ≠ 0 := (Real.log_pos (ha.trans_le hax)).ne'
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)
  have hi1a := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable a ha.le
  have hi1x := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable x hx
  have hiax : IntervalIntegrable (fun t : ℝ => |M t| / t) volume a x :=
    hi1a.symm.trans hi1x
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht
    exact (Real.log_pos (ha.trans_le ht.1)).ne'
  have hiP : IntervalIntegrable
      (fun t : ℝ => (c * A * Real.log t - c * A) / Real.log t ^ 2) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact ((continuousOn_const.mul hl).sub continuousOn_const).div (hl.pow 2)
      (fun t ht => pow_ne_zero 2 (hl0 t ht)) |>.integrableOn_Icc
  have hiupper : (∫ t in a..x, |M t| / t) ≤
      c * A * x / Real.log x - c * A * a / Real.log a := by
    rw [← reciprocal_tail_high_scaled_log_primitive_integral (c * A) a x ha hax]
    apply intervalIntegral.integral_mono_on hax hiax hiP
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have htl := Real.log_pos (ha.trans_le ht.1)
    have hlogt : c ≤ (c - 1) * Real.log t := by
      have hla : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
      have hm := mul_le_mul_of_nonneg_left hla (by linarith : 0 ≤ c - 1)
      linarith
    calc
      |M t| / t ≤ (A * t / Real.log t) / t :=
        div_le_div_of_nonneg_right (hM t ht) htp.le
      _ = A / Real.log t := by field_simp
      _ ≤ (c * A * Real.log t - c * A) / Real.log t ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos htl)).mpr
        have heq : A / Real.log t * Real.log t ^ 2 = A * Real.log t := by
          field_simp
        rw [heq]
        nlinarith [mul_nonneg hA (sub_nonneg.mpr hlogt)]
  have hitotal : (∫ t in (1 : ℝ)..x, |M t| / t) ≤
      C + c * A * x / Real.log x - c * A * a / Real.log a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1a hiax]
    change (∫ t in (1 : ℝ)..a, |M t| / t) ≤ C at hinitial
    linarith
  have hxM : |M x| / x ≤ A / Real.log x := by
    calc
      _ ≤ (A * x / Real.log x) / x :=
        div_le_div_of_nonneg_right (hM x ⟨hax, le_rfl⟩) hxp.le
      _ = _ := by field_simp
  have hi := div_le_div_of_nonneg_right hitotal hxp.le
  have hel := reciprocal_tail_high_moebius_reciprocal_el_marraki_bound x hx
  change |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
    |M x| / x + (∫ t in (1 : ℝ)..x, |M t| / t) / x + Real.log x / x at hel
  have halg : A / Real.log x +
      (C + c * A * x / Real.log x - c * A * a / Real.log a) / x +
      Real.log x / x = (1 + c) * A / Real.log x +
      (C - c * A * a / Real.log a + Real.log x) / x := by
    field_simp
    ring
  rw [← halg]
  linarith

lemma reciprocal_tail_high_logarithmic_square_tail_bound (x : ℝ) (hx : 1200000 ≤ x) :
    Real.log x / x ≤ (1 / 5000) / Real.log x := by
  let T : ℝ := 1200000
  have hTpos : 0 < T := by norm_num [T]
  have hxpos : 0 < x := by linarith
  have hxe : Real.exp 2 ≤ T := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    dsimp only [T]
    nlinarith
  have hTx : T ≤ x := hx
  have hlogT : Real.log T ≤ 15 := by
    apply (Real.log_le_iff_le_exp hTpos).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : T ≤ ∑ i ∈ Finset.range 15, (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [T, Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by norm_num [T])
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : Real.log x / Real.sqrt x ≤ Real.log T / Real.sqrt T :=
    Real.log_div_sqrt_antitoneOn hxe (hxe.trans hTx) hTx
  have hsquare : Real.log x ^ 2 / x ≤ Real.log T ^ 2 / T := by
    have hsq := pow_le_pow_left₀
      (div_nonneg hlogx0 (Real.sqrt_nonneg x)) hsqrt 2
    simpa only [div_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hTpos.le] using hsq
  have hlogT2 : Real.log T ^ 2 ≤ 15 ^ 2 := pow_le_pow_left₀ hlogT0 hlogT 2
  have hbound : Real.log x ^ 2 / x ≤ 1 / 5000 := by
    calc
      _ ≤ Real.log T ^ 2 / T := hsquare
      _ ≤ 15 ^ 2 / T := div_le_div_of_nonneg_right hlogT2 hTpos.le
      _ ≤ _ := by norm_num [T]
  apply (le_div_iff₀ hlogxp).mpr
  convert hbound using 1 <;> first | rfl | ring

theorem reciprocal_tail_high_moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        (7 / 500) * t / Real.log t)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hxa : (1078853 : ℝ) ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga : 0 < Real.log (1078853 : ℝ) := Real.log_pos (by norm_num)
  have hloglo : (27 / 2 : ℝ) ≤ Real.log (1078853 : ℝ) := by
    have h10 : (23 / 10 : ℝ) ≤ Real.log 10 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hmillion : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
      rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 1000000)
      (by norm_num : (1000000 : ℝ) ≤ 1078853)
    rw [hmillion] at hm
    linarith
  have hloghi : Real.log (1078853 : ℝ) ≤ 15 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15) 15
    have hn : (1078853 : ℝ) ≤ ∑ i ∈ Finset.range 15,
        (15 : ℝ) ^ i / Nat.factorial i := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hn.trans hsum
  have h := reciprocal_tail_high_moebius_reciprocal_log_rate_transfer 1078853 x (7 / 500) (27 / 25) 303
    (by norm_num) hxa (by norm_num) (by norm_num) (by nlinarith) hM hinitial
  have hoffset : (303 : ℝ) ≤ (27 / 25) * (7 / 500) * 1078853 /
      Real.log (1078853 : ℝ) := by
    apply (le_div_iff₀ hloga).mpr
    nlinarith
  have herr : (303 - (27 / 25) * (7 / 500) * 1078853 /
      Real.log (1078853 : ℝ) + Real.log x) / x ≤ Real.log x / x :=
    div_le_div_of_nonneg_right (by linarith) hxp.le
  have htail := reciprocal_tail_high_logarithmic_square_tail_bound x hx
  have hmain : (1 + (27 / 25 : ℝ)) * (7 / 500) / Real.log x +
      (1 / 5000) / Real.log x ≤ (3 / 100) / Real.log x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hlogxp.le
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma reciprocal_tail_high_moebius_abs_summatory_trivial_tail (t : ℝ) (ht : 0 ≤ t) :
    |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤ t := by
  calc
    _ ≤ ∑ d ∈ Icc 1 ⌊t⌋₊, |((moebius d : ℤ) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) := by
      apply sum_le_sum
      intro d _
      exact_mod_cast (abs_moebius_le_one (n := d))
    _ = (⌊t⌋₊ : ℝ) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul, mul_one]
    _ ≤ t := Nat.floor_le ht

lemma reciprocal_tail_high_moebius_initial_integral_of_coarse_mertens_tail (B : ℕ) (a : ℝ) (hBnat : 1 ≤ B) (ha : (B : ℝ) ≤ a)
    (hM : ∀ u : ℕ, B ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345) :
    (∫ t in (1 : ℝ)..a,
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ (B : ℝ) + a / 4345 := by
  let b : ℝ := B
  let F : ℝ → ℝ := fun t => |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t
  have hB : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast hBnat
  have hBa : b ≤ a := ha
  have hiB : IntervalIntegrable F volume 1 b := reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable b hB
  have hia : IntervalIntegrable F volume 1 a :=
    reciprocal_tail_high_moebius_abs_summatory_div_intervalIntegrable a (hB.trans hBa)
  have hiBa : IntervalIntegrable F volume b a := hiB.symm.trans hia
  have hsmall : (∫ t in (1 : ℝ)..b, F t) ≤ b - 1 := by
    calc
      _ ≤ ∫ _t in (1 : ℝ)..b, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hB hiB intervalIntegrable_const
        intro t ht
        have htp : 0 < t := by linarith [ht.1]
        dsimp only [F]
        apply (div_le_iff₀ htp).mpr
        simpa only [one_mul] using reciprocal_tail_high_moebius_abs_summatory_trivial_tail t htp.le
      _ = _ := by simp
  have hlarge : (∫ t in b..a, F t) ≤ (a - b) / 4345 := by
    calc
      _ ≤ ∫ _t in b..a, (1 / 4345 : ℝ) := by
        apply intervalIntegral.integral_mono_on hBa hiBa intervalIntegrable_const
        intro t ht
        have htp : 0 < t := by linarith [ht.1]
        have hlo : B ≤ ⌊t⌋₊ := Nat.le_floor ht.1
        have hb := hM ⌊t⌋₊ hlo
        have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htp.le
        have hbound : |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤ t / 4345 :=
          hb.trans (div_le_div_of_nonneg_right hfloor (by norm_num))
        dsimp only [F]
        apply (div_le_iff₀ htp).mpr
        convert hbound using 1 <;> first | rfl | ring
      _ = _ := by simp [div_eq_mul_inv]
  change (∫ t in (1 : ℝ)..a, F t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hiB hiBa]
  dsimp only [b] at hsmall hlarge ⊢
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

theorem moebius_reciprocal_high_of_prime_errors_and_tail_mertens_complete
    (x C : ℝ) (hx : 10000000000000000000000000000 ≤ x) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (hM : ∀ u : ℕ, 10000000000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100) / Real.log x := by
  let a : ℝ := 10000000000000000000000000000
  have ha : 1 < a := by norm_num [a]
  have hax : a ≤ x := hx
  have hxp : 0 < x := by linarith
  have hlogxp : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogten : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlogalo : (322 / 5 : ℝ) ≤ Real.log a := by
    rw [show a = (10 : ℝ) ^ (28 : ℕ) by norm_num [a], Real.log_pow, hlogten]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogahi : Real.log a ≤ 65 := by
    rw [show a = (10 : ℝ) ^ (28 : ℕ) by norm_num [a], Real.log_pow, hlogten]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hMhigh : ∀ t ∈ Set.Icc a x,
      |∑ d ∈ Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤ (7 / 500) * t / Real.log t := by
    intro t ht
    exact reciprocal_tail_high_moebius_summatory_high_of_prime_errors_and_tail_mertens t C ht.1 hC hRhigh hRmiddle hM
  have hinitial := reciprocal_tail_high_moebius_initial_integral_of_coarse_mertens_tail 10000000000000000 a (by norm_num) (by norm_num [a]) hM
  have hb := reciprocal_tail_high_moebius_reciprocal_log_rate_transfer a x (7 / 500) (27 / 25)
    (10000000000000000 + a / 4345) ha hax (by norm_num) (by norm_num) (by nlinarith) hMhigh hinitial
  have hoffset : 10000000000000000 + a / 4345 ≤ (27 / 25) * (7 / 500) * a / Real.log a := by
    apply (le_div_iff₀ hloga).mpr
    have hm := mul_le_mul_of_nonneg_left hlogahi (by positivity : 0 ≤ 10000000000000000 + a / 4345)
    have hn : (10000000000000000 + a / 4345) * 65 ≤ (27 / 25) * (7 / 500) * a := by norm_num [a]
    exact hm.trans hn
  have herr : (10000000000000000 + a / 4345 - (27 / 25) * (7 / 500) * a / Real.log a + Real.log x) / x ≤
      Real.log x / x := div_le_div_of_nonneg_right (by linarith) hxp.le
  have htail := reciprocal_tail_high_logarithmic_square_tail_bound x (by linarith [hx] : 1200000 ≤ x)
  have hmain : (1 + (27 / 25 : ℝ)) * (7 / 500) / Real.log x +
      (1 / 5000) / Real.log x ≤ (3 / 100) / Real.log x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hlogxp.le
  linarith

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution 
    (x C : ℝ) (hx : 10000000000000000000000000000 ≤ x) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (hM : ∀ u : ℕ, 10000000000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100) / Real.log x := Helfgott.moebius_reciprocal_high_of_prime_errors_and_tail_mertens_complete x C hx hC hRhigh hRmiddle hM
#print axioms solution
