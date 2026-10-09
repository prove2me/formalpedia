-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_decay_of_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:18:30.872868+00:00
-- url     : https://prove2.me/submissions/4df7a52f-c429-4a33-8940-e3a04fc9bac1

import Definitions.Def_Helfgott_MobiusReciprocalCertificate
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Helfgott

lemma mobiusRoundedPrefix_succ (g : ℕ → ℤ) (Q n : ℕ) :
    mobiusRoundedPrefix g Q (n + 1) = mobiusRoundedPrefix g Q n + g n * (Q / n : ℕ) := by
  simp only [mobiusRoundedPrefix, Finset.sum_range_succ]

lemma mobiusReciprocalScan_finish (g : ℕ → ℤ) (Q A B K fuel offset : ℕ) (s : ℤ)
    (hs : s = mobiusRoundedPrefix g Q (min B offset)) :
    (mobiusReciprocalScan g Q A B K fuel offset s).2 =
      mobiusRoundedPrefix g Q (min B (offset + fuel)) := by
  induction fuel generalizing offset s with
  | zero => simpa [mobiusReciprocalScan] using hs
  | succ fuel ih =>
      by_cases hoff : offset < B
      · have hmin : min B offset = offset := min_eq_right hoff.le
        have hminnext : min B (offset + 1) = offset + 1 := min_eq_right (by omega)
        have hnext : s + g offset * (Q / offset : ℕ) =
            mobiusRoundedPrefix g Q (min B (offset + 1)) := by
          rw [hminnext, mobiusRoundedPrefix_succ, hs, hmin]
        simpa only [mobiusReciprocalScan, hoff, if_pos, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using ih (offset + 1) _ hnext
      · have hb : B ≤ offset := by omega
        have hmin : min B offset = B := min_eq_left hb
        have hminend : min B (offset + (fuel + 1)) = B := min_eq_left (by omega)
        simp only [mobiusReciprocalScan, hoff, if_false, hminend]
        simpa only [hmin] using hs

lemma mobiusReciprocalScan_bound (g : ℕ → ℤ) (Q A B K fuel offset : ℕ) (s : ℤ)
    (hs : s = mobiusRoundedPrefix g Q (min B offset))
    (hc : (mobiusReciprocalScan g Q A B K fuel offset s).1 = true) :
    ∀ n, offset ≤ n → n < offset + fuel → A ≤ n → n < B →
      10 * ((mobiusRoundedPrefix g Q (n + 1)).natAbs + n) * K ≤ 3 * Q := by
  induction fuel generalizing offset s with
  | zero => intro n hlo hup; omega
  | succ fuel ih =>
      intro n hlo hup hA hnB
      have hoff : offset < B := lt_of_le_of_lt hlo hnB
      have hmin : min B offset = offset := min_eq_right hoff.le
      have hminnext : min B (offset + 1) = offset + 1 := min_eq_right (by omega)
      have hnext : s + g offset * (Q / offset : ℕ) =
          mobiusRoundedPrefix g Q (min B (offset + 1)) := by
        rw [hminnext, mobiusRoundedPrefix_succ, hs, hmin]
      have hh : (if A ≤ offset then
          decide (10 * ((s + g offset * (Q / offset : ℕ)).natAbs + offset) * K ≤ 3 * Q)
          else true) = true ∧
          (mobiusReciprocalScan g Q A B K fuel (offset + 1)
            (s + g offset * (Q / offset : ℕ))).1 = true := by
        simpa only [mobiusReciprocalScan, hoff, if_pos, Bool.and_eq_true] using hc
      by_cases heq : n = offset
      · subst n
        have hnum : 10 * ((s + g offset * (Q / offset : ℕ)).natAbs + offset) * K ≤ 3 * Q := by
          simpa only [hA, if_pos, decide_eq_true_eq] using hh.1
        simpa only [hnext, hminnext] using hnum
      · apply ih (offset + 1) _ hnext hh.2 n (by omega) (by omega) hA hnB

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Real
open scoped BigOperators
namespace Helfgott

private lemma reciprocalLog94 : Real.log (12088 : ℝ) ≤ (94 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 12088)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 94 / 10) 70
  have hq : (12088 : ℚ) ≤ ∑ i ∈ Finset.range 70, (94 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (12088 : ℝ) ≤ ∑ i ∈ Finset.range 70, (94 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog95 : Real.log (13359 : ℝ) ≤ (95 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 13359)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 95 / 10) 70
  have hq : (13359 : ℚ) ≤ ∑ i ∈ Finset.range 70, (95 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (13359 : ℝ) ≤ ∑ i ∈ Finset.range 70, (95 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog96 : Real.log (14764 : ℝ) ≤ (96 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 14764)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 96 / 10) 70
  have hq : (14764 : ℚ) ≤ ∑ i ∈ Finset.range 70, (96 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (14764 : ℝ) ≤ ∑ i ∈ Finset.range 70, (96 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog97 : Real.log (16317 : ℝ) ≤ (97 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 16317)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 97 / 10) 70
  have hq : (16317 : ℚ) ≤ ∑ i ∈ Finset.range 70, (97 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (16317 : ℝ) ≤ ∑ i ∈ Finset.range 70, (97 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog98 : Real.log (18033 : ℝ) ≤ (98 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 18033)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 98 / 10) 70
  have hq : (18033 : ℚ) ≤ ∑ i ∈ Finset.range 70, (98 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (18033 : ℝ) ≤ ∑ i ∈ Finset.range 70, (98 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog99 : Real.log (19930 : ℝ) ≤ (99 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 19930)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 10) 70
  have hq : (19930 : ℚ) ≤ ∑ i ∈ Finset.range 70, (99 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (19930 : ℝ) ≤ ∑ i ∈ Finset.range 70, (99 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog100 : Real.log (22026 : ℝ) ≤ (100 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22026)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 100 / 10) 70
  have hq : (22026 : ℚ) ≤ ∑ i ∈ Finset.range 70, (100 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (22026 : ℝ) ≤ ∑ i ∈ Finset.range 70, (100 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog101 : Real.log (24343 : ℝ) ≤ (101 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 24343)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 101 / 10) 70
  have hq : (24343 : ℚ) ≤ ∑ i ∈ Finset.range 70, (101 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (24343 : ℝ) ≤ ∑ i ∈ Finset.range 70, (101 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog102 : Real.log (26903 : ℝ) ≤ (102 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 26903)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 102 / 10) 70
  have hq : (26903 : ℚ) ≤ ∑ i ∈ Finset.range 70, (102 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (26903 : ℝ) ≤ ∑ i ∈ Finset.range 70, (102 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog103 : Real.log (29732 : ℝ) ≤ (103 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 29732)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 103 / 10) 70
  have hq : (29732 : ℚ) ≤ ∑ i ∈ Finset.range 70, (103 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (29732 : ℝ) ≤ ∑ i ∈ Finset.range 70, (103 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog104 : Real.log (32859 : ℝ) ≤ (104 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 32859)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 104 / 10) 70
  have hq : (32859 : ℚ) ≤ ∑ i ∈ Finset.range 70, (104 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (32859 : ℝ) ≤ ∑ i ∈ Finset.range 70, (104 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog105 : Real.log (36315 : ℝ) ≤ (105 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 36315)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 105 / 10) 70
  have hq : (36315 : ℚ) ≤ ∑ i ∈ Finset.range 70, (105 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (36315 : ℝ) ≤ ∑ i ∈ Finset.range 70, (105 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog106 : Real.log (40134 : ℝ) ≤ (106 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 40134)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 106 / 10) 70
  have hq : (40134 : ℚ) ≤ ∑ i ∈ Finset.range 70, (106 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (40134 : ℝ) ≤ ∑ i ∈ Finset.range 70, (106 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog107 : Real.log (44355 : ℝ) ≤ (107 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 44355)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 107 / 10) 70
  have hq : (44355 : ℚ) ≤ ∑ i ∈ Finset.range 70, (107 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (44355 : ℝ) ≤ ∑ i ∈ Finset.range 70, (107 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog108 : Real.log (49020 : ℝ) ≤ (108 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 49020)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 108 / 10) 70
  have hq : (49020 : ℚ) ≤ ∑ i ∈ Finset.range 70, (108 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (49020 : ℝ) ≤ ∑ i ∈ Finset.range 70, (108 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog109 : Real.log (54176 : ℝ) ≤ (109 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 54176)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 109 / 10) 70
  have hq : (54176 : ℚ) ≤ ∑ i ∈ Finset.range 70, (109 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (54176 : ℝ) ≤ ∑ i ∈ Finset.range 70, (109 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog110 : Real.log (59874 : ℝ) ≤ (110 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 59874)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 110 / 10) 70
  have hq : (59874 : ℚ) ≤ ∑ i ∈ Finset.range 70, (110 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (59874 : ℝ) ≤ ∑ i ∈ Finset.range 70, (110 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog111 : Real.log (66171 : ℝ) ≤ (111 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 66171)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 10) 70
  have hq : (66171 : ℚ) ≤ ∑ i ∈ Finset.range 70, (111 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (66171 : ℝ) ≤ ∑ i ∈ Finset.range 70, (111 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog112 : Real.log (73130 : ℝ) ≤ (112 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 73130)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 112 / 10) 70
  have hq : (73130 : ℚ) ≤ ∑ i ∈ Finset.range 70, (112 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (73130 : ℝ) ≤ ∑ i ∈ Finset.range 70, (112 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog113 : Real.log (80821 : ℝ) ≤ (113 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 80821)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 113 / 10) 70
  have hq : (80821 : ℚ) ≤ ∑ i ∈ Finset.range 70, (113 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (80821 : ℝ) ≤ ∑ i ∈ Finset.range 70, (113 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog114 : Real.log (89321 : ℝ) ≤ (114 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 89321)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 114 / 10) 70
  have hq : (89321 : ℚ) ≤ ∑ i ∈ Finset.range 70, (114 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (89321 : ℝ) ≤ ∑ i ∈ Finset.range 70, (114 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog115 : Real.log (98715 : ℝ) ≤ (115 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 98715)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 10) 70
  have hq : (98715 : ℚ) ≤ ∑ i ∈ Finset.range 70, (115 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (98715 : ℝ) ≤ ∑ i ∈ Finset.range 70, (115 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog116 : Real.log (109097 : ℝ) ≤ (116 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 109097)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 116 / 10) 70
  have hq : (109097 : ℚ) ≤ ∑ i ∈ Finset.range 70, (116 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (109097 : ℝ) ≤ ∑ i ∈ Finset.range 70, (116 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog117 : Real.log (120571 : ℝ) ≤ (117 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 120571)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 117 / 10) 70
  have hq : (120571 : ℚ) ≤ ∑ i ∈ Finset.range 70, (117 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (120571 : ℝ) ≤ ∑ i ∈ Finset.range 70, (117 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog118 : Real.log (133252 : ℝ) ≤ (118 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 133252)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 118 / 10) 70
  have hq : (133252 : ℚ) ≤ ∑ i ∈ Finset.range 70, (118 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (133252 : ℝ) ≤ ∑ i ∈ Finset.range 70, (118 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog119 : Real.log (147266 : ℝ) ≤ (119 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 147266)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 119 / 10) 70
  have hq : (147266 : ℚ) ≤ ∑ i ∈ Finset.range 70, (119 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (147266 : ℝ) ≤ ∑ i ∈ Finset.range 70, (119 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog120 : Real.log (162754 : ℝ) ≤ (120 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 162754)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 120 / 10) 70
  have hq : (162754 : ℚ) ≤ ∑ i ∈ Finset.range 70, (120 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (162754 : ℝ) ≤ ∑ i ∈ Finset.range 70, (120 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog121 : Real.log (179871 : ℝ) ≤ (121 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 179871)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 121 / 10) 70
  have hq : (179871 : ℚ) ≤ ∑ i ∈ Finset.range 70, (121 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (179871 : ℝ) ≤ ∑ i ∈ Finset.range 70, (121 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog122 : Real.log (198789 : ℝ) ≤ (122 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 198789)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 122 / 10) 70
  have hq : (198789 : ℚ) ≤ ∑ i ∈ Finset.range 70, (122 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (198789 : ℝ) ≤ ∑ i ∈ Finset.range 70, (122 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog123 : Real.log (219695 : ℝ) ≤ (123 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 219695)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 123 / 10) 70
  have hq : (219695 : ℚ) ≤ ∑ i ∈ Finset.range 70, (123 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (219695 : ℝ) ≤ ∑ i ∈ Finset.range 70, (123 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog124 : Real.log (242801 : ℝ) ≤ (124 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 242801)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 124 / 10) 70
  have hq : (242801 : ℚ) ≤ ∑ i ∈ Finset.range 70, (124 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (242801 : ℝ) ≤ ∑ i ∈ Finset.range 70, (124 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog125 : Real.log (268337 : ℝ) ≤ (125 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 268337)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 125 / 10) 70
  have hq : (268337 : ℚ) ≤ ∑ i ∈ Finset.range 70, (125 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (268337 : ℝ) ≤ ∑ i ∈ Finset.range 70, (125 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog126 : Real.log (296558 : ℝ) ≤ (126 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 296558)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 126 / 10) 70
  have hq : (296558 : ℚ) ≤ ∑ i ∈ Finset.range 70, (126 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (296558 : ℝ) ≤ ∑ i ∈ Finset.range 70, (126 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog127 : Real.log (327747 : ℝ) ≤ (127 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 327747)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 127 / 10) 70
  have hq : (327747 : ℚ) ≤ ∑ i ∈ Finset.range 70, (127 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (327747 : ℝ) ≤ ∑ i ∈ Finset.range 70, (127 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog128 : Real.log (362217 : ℝ) ≤ (128 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 362217)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 128 / 10) 70
  have hq : (362217 : ℚ) ≤ ∑ i ∈ Finset.range 70, (128 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (362217 : ℝ) ≤ ∑ i ∈ Finset.range 70, (128 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog129 : Real.log (400312 : ℝ) ≤ (129 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 400312)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 129 / 10) 70
  have hq : (400312 : ℚ) ≤ ∑ i ∈ Finset.range 70, (129 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (400312 : ℝ) ≤ ∑ i ∈ Finset.range 70, (129 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog130 : Real.log (442413 : ℝ) ≤ (130 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 442413)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 130 / 10) 70
  have hq : (442413 : ℚ) ≤ ∑ i ∈ Finset.range 70, (130 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (442413 : ℝ) ≤ ∑ i ∈ Finset.range 70, (130 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog131 : Real.log (488942 : ℝ) ≤ (131 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 488942)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 131 / 10) 70
  have hq : (488942 : ℚ) ≤ ∑ i ∈ Finset.range 70, (131 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (488942 : ℝ) ≤ ∑ i ∈ Finset.range 70, (131 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog132 : Real.log (540364 : ℝ) ≤ (132 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 540364)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 132 / 10) 70
  have hq : (540364 : ℚ) ≤ ∑ i ∈ Finset.range 70, (132 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (540364 : ℝ) ≤ ∑ i ∈ Finset.range 70, (132 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog133 : Real.log (597195 : ℝ) ≤ (133 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 597195)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 133 / 10) 70
  have hq : (597195 : ℚ) ≤ ∑ i ∈ Finset.range 70, (133 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (597195 : ℝ) ≤ ∑ i ∈ Finset.range 70, (133 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog134 : Real.log (660003 : ℝ) ≤ (134 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 660003)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 134 / 10) 70
  have hq : (660003 : ℚ) ≤ ∑ i ∈ Finset.range 70, (134 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (660003 : ℝ) ≤ ∑ i ∈ Finset.range 70, (134 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog135 : Real.log (729416 : ℝ) ≤ (135 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 729416)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 135 / 10) 70
  have hq : (729416 : ℚ) ≤ ∑ i ∈ Finset.range 70, (135 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (729416 : ℝ) ≤ ∑ i ∈ Finset.range 70, (135 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog136 : Real.log (806129 : ℝ) ≤ (136 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 806129)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 136 / 10) 70
  have hq : (806129 : ℚ) ≤ ∑ i ∈ Finset.range 70, (136 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (806129 : ℝ) ≤ ∑ i ∈ Finset.range 70, (136 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog137 : Real.log (890911 : ℝ) ≤ (137 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 890911)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 137 / 10) 70
  have hq : (890911 : ℚ) ≤ ∑ i ∈ Finset.range 70, (137 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (890911 : ℝ) ≤ ∑ i ∈ Finset.range 70, (137 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog138 : Real.log (984609 : ℝ) ≤ (138 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 984609)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 138 / 10) 70
  have hq : (984609 : ℚ) ≤ ∑ i ∈ Finset.range 70, (138 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (984609 : ℝ) ≤ ∑ i ∈ Finset.range 70, (138 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog139 : Real.log (1088161 : ℝ) ≤ (139 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1088161)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 139 / 10) 70
  have hq : (1088161 : ℚ) ≤ ∑ i ∈ Finset.range 70, (139 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (1088161 : ℝ) ≤ ∑ i ∈ Finset.range 70, (139 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog140 : Real.log (1202604 : ℝ) ≤ (140 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1202604)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 140 / 10) 70
  have hq : (1202604 : ℚ) ≤ ∑ i ∈ Finset.range 70, (140 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (1202604 : ℝ) ≤ ∑ i ∈ Finset.range 70, (140 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

theorem reciprocal_certificate_log_grid : ∀ c ∈ ([(94, 12088), (95, 13359), (96, 14764), (97, 16317), (98, 18033), (99, 19930), (100, 22026), (101, 24343), (102, 26903), (103, 29732), (104, 32859), (105, 36315), (106, 40134), (107, 44355), (108, 49020), (109, 54176), (110, 59874), (111, 66171), (112, 73130), (113, 80821), (114, 89321), (115, 98715), (116, 109097), (117, 120571), (118, 133252), (119, 147266), (120, 162754), (121, 179871), (122, 198789), (123, 219695), (124, 242801), (125, 268337), (126, 296558), (127, 327747), (128, 362217), (129, 400312), (130, 442413), (131, 488942), (132, 540364), (133, 597195), (134, 660003), (135, 729416), (136, 806129), (137, 890911), (138, 984609), (139, 1088161), (140, 1202604)] : List (ℕ × ℕ)), Real.log (c.2 : ℝ) ≤ (c.1 : ℝ) / 10 := by
  simp only [List.forall_mem_cons]
  exact ⟨reciprocalLog94, reciprocalLog95, reciprocalLog96, reciprocalLog97, reciprocalLog98, reciprocalLog99, reciprocalLog100, reciprocalLog101, reciprocalLog102, reciprocalLog103, reciprocalLog104, reciprocalLog105, reciprocalLog106, reciprocalLog107, reciprocalLog108, reciprocalLog109, reciprocalLog110, reciprocalLog111, reciprocalLog112, reciprocalLog113, reciprocalLog114, reciprocalLog115, reciprocalLog116, reciprocalLog117, reciprocalLog118, reciprocalLog119, reciprocalLog120, reciprocalLog121, reciprocalLog122, reciprocalLog123, reciprocalLog124, reciprocalLog125, reciprocalLog126, reciprocalLog127, reciprocalLog128, reciprocalLog129, reciprocalLog130, reciprocalLog131, reciprocalLog132, reciprocalLog133, reciprocalLog134, reciprocalLog135, reciprocalLog136, reciprocalLog137, reciprocalLog138, reciprocalLog139, reciprocalLog140, List.forall_mem_nil _⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace Helfgott

lemma mobiusReciprocalLogGrid_sound (c : ℕ × ℕ) (hc : c ∈ mobiusReciprocalLogGrid) :
    Real.log (c.2 : ℝ) ≤ (c.1 : ℝ) / 10 :=
  reciprocal_certificate_log_grid c hc

lemma mobiusReciprocalTree_finish_of_past_bound (g : ℕ → ℤ) (Q A B d offset : ℕ)
    (tree : MobiusReciprocalTree) (hoff : B ≤ offset)
    (hs : mobiusReciprocalStart tree = mobiusRoundedPrefix g Q (min B offset))
    (hc : mobiusReciprocalTreeCheck g Q A B d offset tree = true) :
    mobiusReciprocalFinish tree = mobiusRoundedPrefix g Q (min B (offset + 32 * 2 ^ d)) := by
  unfold mobiusReciprocalTreeCheck at hc
  simp only [hoff, if_pos, beq_iff_eq] at hc
  have hend : min B (offset + 32 * 2 ^ d) = B := min_eq_left (by omega)
  rw [← hc, hs, min_eq_left hoff, hend]

lemma mobiusReciprocalTree_finish (g : ℕ → ℤ) (Q A B d offset : ℕ)
    (tree : MobiusReciprocalTree)
    (hs : mobiusReciprocalStart tree = mobiusRoundedPrefix g Q (min B offset))
    (hc : mobiusReciprocalTreeCheck g Q A B d offset tree = true) :
    mobiusReciprocalFinish tree = mobiusRoundedPrefix g Q (min B (offset + 32 * 2 ^ d)) := by
  induction d generalizing offset tree with
  | zero =>
      by_cases hoff : B ≤ offset
      · exact mobiusReciprocalTree_finish_of_past_bound g Q A B 0 offset tree hoff hs hc
      · cases tree with
        | leaf start finish K T =>
            have hh : (mobiusReciprocalScan g Q A B K 32 offset start).1 = true ∧
                (mobiusReciprocalScan g Q A B K 32 offset start).2 = finish := by
              have hleaf : mobiusReciprocalLeafCheck g Q A B offset K T start finish = true := by
                simpa only [mobiusReciprocalTreeCheck, hoff, if_false] using hc
              have hfields := hleaf
              simp only [mobiusReciprocalLeafCheck, Bool.and_eq_true, beq_iff_eq] at hfields
              exact hfields.1
            have hend := mobiusReciprocalScan_finish g Q A B K 32 offset start hs
            simpa only [mobiusReciprocalFinish, pow_zero, mul_one] using hh.2.symm.trans hend
        | branch l r =>
            unfold mobiusReciprocalTreeCheck at hc
            simp only [hoff, if_false] at hc
            contradiction
  | succ d ih =>
      by_cases hoff : B ≤ offset
      · exact mobiusReciprocalTree_finish_of_past_bound g Q A B (d + 1) offset tree hoff hs hc
      · cases tree with
        | leaf start finish K T =>
            unfold mobiusReciprocalTreeCheck at hc
            simp only [hoff, if_false] at hc
            contradiction
        | branch l r =>
            have hh : mobiusReciprocalTreeCheck g Q A B d offset l = true ∧
                mobiusReciprocalTreeCheck g Q A B d (offset + 32 * 2 ^ d) r = true ∧
                mobiusReciprocalFinish l = mobiusReciprocalStart r := by
              simpa only [mobiusReciprocalTreeCheck, hoff, if_false, Bool.and_assoc,
                Bool.and_eq_true, beq_iff_eq, and_assoc] using hc
            have hl := ih offset l hs hh.1
            have hsr : mobiusReciprocalStart r =
                mobiusRoundedPrefix g Q (min B (offset + 32 * 2 ^ d)) := hh.2.2.symm.trans hl
            have hr := ih (offset + 32 * 2 ^ d) r hsr hh.2.1
            have hspan : offset + 32 * 2 ^ d + 32 * 2 ^ d = offset + 32 * 2 ^ (d + 1) := by
              rw [pow_succ]; ring
            simpa only [mobiusReciprocalFinish, hspan] using hr

theorem mobiusReciprocalTree_integer_bounds (g : ℕ → ℤ) (Q A B d offset : ℕ)
    (tree : MobiusReciprocalTree)
    (hs : mobiusReciprocalStart tree = mobiusRoundedPrefix g Q (min B offset))
    (hc : mobiusReciprocalTreeCheck g Q A B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → A ≤ n → n < B →
      ∃ K : ℕ,
        10 * ((mobiusRoundedPrefix g Q (n + 1)).natAbs + n) * K ≤ 3 * Q ∧
        Real.log ((n + 1 : ℕ) : ℝ) ≤ (K : ℝ) / 10 := by
  induction d generalizing offset tree with
  | zero =>
      intro n hlo hup hA hnB
      have hoff : ¬B ≤ offset := by omega
      simp only [pow_zero, mul_one] at hup
      cases tree with
      | leaf start finish K T =>
          have hactive : A < offset + 32 ∧ offset < B := by omega
          have hh : (mobiusReciprocalScan g Q A B K 32 offset start).1 = true ∧
              (mobiusReciprocalScan g Q A B K 32 offset start).2 = finish ∧
              (K, T) ∈ mobiusReciprocalLogGrid ∧ offset + 32 ≤ T := by
            simpa only [mobiusReciprocalTreeCheck, hoff, if_false, mobiusReciprocalLeafCheck,
              hactive, and_self, and_true, true_and, if_pos, Bool.and_assoc, Bool.and_eq_true, beq_iff_eq,
              decide_eq_true_eq, and_assoc] using hc
          have hnum := mobiusReciprocalScan_bound g Q A B K 32 offset start hs hh.1 n hlo hup hA hnB
          have hlog := mobiusReciprocalLogGrid_sound (K, T) hh.2.2.1
          have hnt : n + 1 ≤ T := by omega
          have hlogn : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (T : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hnt)
          exact ⟨K, hnum, hlogn.trans hlog⟩
      | branch l r =>
          unfold mobiusReciprocalTreeCheck at hc
          simp only [hoff, if_false] at hc
          contradiction
  | succ d ih =>
      intro n hlo hup hA hnB
      have hoff : ¬B ≤ offset := by omega
      cases tree with
      | leaf start finish K T =>
          unfold mobiusReciprocalTreeCheck at hc
          simp only [hoff, if_false] at hc
          contradiction
      | branch l r =>
          have hh : mobiusReciprocalTreeCheck g Q A B d offset l = true ∧
              mobiusReciprocalTreeCheck g Q A B d (offset + 32 * 2 ^ d) r = true ∧
              mobiusReciprocalFinish l = mobiusReciprocalStart r := by
            simpa only [mobiusReciprocalTreeCheck, hoff, if_false, Bool.and_assoc,
              Bool.and_eq_true, beq_iff_eq, and_assoc] using hc
          by_cases hleft : n < offset + 32 * 2 ^ d
          · exact ih offset l hs hh.1 n hlo hleft hA hnB
          · have hl := mobiusReciprocalTree_finish g Q A B d offset l hs hh.1
            have hsr : mobiusReciprocalStart r =
                mobiusRoundedPrefix g Q (min B (offset + 32 * 2 ^ d)) := hh.2.2.symm.trans hl
            have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by rw [pow_succ]; ring
            rw [hspan] at hup
            exact ih (offset + 32 * 2 ^ d) r hsr hh.2.1 n (by omega) (by omega) hA hnB

end Helfgott
end

section
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
namespace Helfgott

-- A proper small divisor disqualifies every composite; only the prime cases need membership.
def mobiusSmallPrimeCompletenessCheck : Bool :=
  (List.range 1101).all (fun n =>
    decide (n < 2) ||
      ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).any
        (fun d => decide (2 ≤ d) && decide (d < n) && (n % d == 0)) ||
      decide (n ∈ mobiusSmallPrimes))

lemma mobiusSmallPrimeCompletenessCheck_checked :
    mobiusSmallPrimeCompletenessCheck = true := by decide +kernel

lemma mobiusSmallPrimes_complete_fast :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes := by
  intro p hp
  have hc := List.all_eq_true.mp mobiusSmallPrimeCompletenessCheck_checked
    p.val (by simpa using p.isLt)
  have fields : p.val < 2 ∨
      (∃ d ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ),
        2 ≤ d ∧ d < p.val ∧ p.val % d = 0) ∨ p.val ∈ mobiusSmallPrimes := by
    simpa [mobiusSmallPrimeCompletenessCheck, List.any_eq_true, Bool.or_assoc, or_assoc,
      Bool.and_assoc, and_assoc] using hc
  rcases fields with hsmall | hdiv | hmem
  · have hp2 := hp.two_le
    omega
  · obtain ⟨d, hdL, hd2, hdp, hdmod⟩ := hdiv
    exact False.elim ((Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdmod) hd2 hdp) hp)
  · exact hmem

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

lemma mobiusSmallPrimes_sound : ∀ p ∈ mobiusSmallPrimes, Nat.Prime p := by
  simp only [mobiusSmallPrimes, List.forall_mem_cons]
  exact ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma mobiusSmallPrimes_complete :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes :=
  mobiusSmallPrimes_complete_fast

lemma mobiusSmallPrimeCheck_sound (n : ℕ) (hn : n < 1200001)
    (hc : mobiusSmallPrimeCheck n = true) : Nat.Prime n := by
  have hcfields : 2 ≤ n ∧ mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true := by
    simpa [mobiusSmallPrimeCheck] using hc
  have hn2 : 2 ≤ n := hcfields.1
  by_contra hnot
  let p := n.minFac
  have hpp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnot
  have hpbound : p < 1101 := by nlinarith
  have hmem : p ∈ mobiusSmallPrimes := mobiusSmallPrimes_complete ⟨p, hpbound⟩ hpp
  have hall : mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true :=
    hcfields.2
  have hpcheck := List.all_eq_true.mp hall p hmem
  have hdiv : n % p = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  simp [show p * p ≤ n by simpa [pow_two] using hpsq, hdiv] at hpcheck

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

theorem moebius_of_local_checks (g : ℕ → ℤ) (B : ℕ) (hB : B ≤ 1200001)
    (hc : ∀ n < B, ∃ p, mobiusLocalCheck g n p = true) :
    ∀ n < B, g n = moebius n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnB
    obtain ⟨p, hpcheck⟩ := hc n hnB
    by_cases hn0 : n = 0
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hn1 : n = 1
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hp0 : p = 0
    · subst p
      have hh : mobiusSmallPrimeCheck n = true ∧ g n = -1 := by
        simpa [mobiusLocalCheck, hn0, hn1] using hpcheck
      have hp := mobiusSmallPrimeCheck_sound n (lt_of_lt_of_le hnB hB) hh.1
      rw [hh.2, moebius_apply_prime hp]
    have hfields : p ∈ mobiusSmallPrimes ∧ p < n ∧ n % p = 0 ∧
        g n = (if (n / p) % p == 0 then 0 else -g (n / p)) := by
      simpa [mobiusLocalCheck, hn0, hn1, hp0, Bool.and_assoc, and_assoc] using hpcheck
    obtain ⟨hpL, hpn, hdiv, hvalue⟩ := hfields
    have hpp := mobiusSmallPrimes_sound p hpL
    have hnp : p ∣ n := Nat.dvd_of_mod_eq_zero hdiv
    have hprod : p * (n / p) = n := Nat.mul_div_cancel' hnp
    have hp2 : 2 ≤ p := hpp.two_le
    have hquot : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
    have hrec := ih (n / p) hquot (lt_trans hquot hnB)
    by_cases hq : (n / p) % p = 0
    · have hpsq : p ^ 2 ∣ n := by
        rw [← hprod, pow_two]
        exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mod_eq_zero hq)
      have hnsq : ¬Squarefree n := by
        intro hs
        have hp2 := hs.squarefree_of_dvd hpsq
        have hf := (Nat.squarefree_pow_iff hpp.ne_one (by norm_num : (2 : ℕ) ≠ 0)).mp hp2
        norm_num at hf
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simpa [hq] using hvalue
    · have hcop : Nat.Coprime p (n / p) := hpp.coprime_iff_not_dvd.mpr
        (fun hd => hq (Nat.mod_eq_zero_of_dvd hd))
      rw [← hprod, isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hpp]
      simpa [hprod, hq, hrec] using hvalue

lemma mobiusTreeCheck_local_sound (g : ℕ → ℤ) (B d offset : ℕ) (tree : MobiusCertTree)
    (hc : mobiusTreeCheck g B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      ∃ p, mobiusLocalCheck g n p = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits =>
      have hh : mobiusLeafCheck g B offset factorDigits = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hh (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      simp only [mobiusLeafCheck] at hh
      rw [he, if_pos hnB] at hlocal
      exact ⟨_, hlocal⟩
    | branch l r => simp [mobiusTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits => simp [mobiusTreeCheck, hoff] at hc
    | branch l r =>
      have hh : mobiusTreeCheck g B d offset l = true ∧
          mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2 n (by omega) (by omega) hnB

theorem mobiusTreeCheck_sound (B d : ℕ) (tree : MobiusCertTree)
    (hB : B ≤ 1200001) (hcapacity : B ≤ 32 * 2 ^ d)
    (hc : mobiusTreeCheck (mobiusTreeValue d tree) B d 0 tree = true) :
    ∀ n < B, mobiusTreeValue d tree n = moebius n := by
  apply moebius_of_local_checks _ B hB
  intro n hn
  exact mobiusTreeCheck_local_sound _ B d 0 tree hc n (Nat.zero_le n)
    (by simpa using lt_of_lt_of_le hn hcapacity) hn

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma mobiusHarmonicCeil_bound (Q n : ℕ) (s : ℤ) (hQ : 0 < Q) :
    |(s : ℝ)| / (n : ℝ) ≤ (mobiusHarmonicCeil Q n s : ℝ) / (Q : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, mobiusHarmonicCeil]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmod := Nat.mod_lt (s.natAbs * Q + n - 1) hnpos
  have hdiv := Nat.div_add_mod (s.natAbs * Q + n - 1) n
  rw [Nat.mul_comm n ((s.natAbs * Q + n - 1) / n)] at hdiv
  have hmul : s.natAbs * Q ≤ ((s.natAbs * Q + n - 1) / n) * n := by
    omega
  have hcast : |(s : ℝ)| * (Q : ℝ) ≤
      (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
    have hcast0 : (s.natAbs : ℝ) * (Q : ℝ) ≤
        (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
      exact_mod_cast hmul
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [mobiusHarmonicCeil, if_neg hn]
  exact (div_le_div_iff₀ hnR hQR).mpr hcast

lemma prefix_of_local_checks (g M : ℕ → ℤ) (B : ℕ)
    (hc : ∀ n < B, mobiusPrefixLocalCheck g M n = true) :
    ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hh := hc 0 hn
    simpa [mobiusPrefixLocalCheck] using hh
  | succ n ih =>
    intro hn
    have hh := hc (n + 1) hn
    have hs : M (n + 1) = M n + g (n + 1) := by
      simpa [mobiusPrefixLocalCheck] using hh
    rw [hs, ih (by omega), Finset.sum_range_succ (f := g) (n := n + 1)]

lemma mobiusHarmonicTreeCheck_local_sound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      mobiusPrefixLocalCheck g M n = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have hall : (List.range 32).all (fun k =>
          if offset + k < B then mobiusPrefixLocalCheck g M (offset + k) else true) = true :=
        (Bool.and_eq_true_iff.mp hh).1
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hall (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      rwa [he, if_pos hnB] at hlocal
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2.1 n (by omega) (by omega) hnB

lemma mobiusHarmonicTreeCheck_bound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree) (hQ : 0 < Q)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    (∑ k ∈ Finset.range (32 * 2 ^ d),
      if offset + k < B then |(M (offset + k) : ℝ)| / (offset + k : ℕ) else 0) ≤
      (mobiusHarmonicUpper tree : ℝ) / (Q : ℝ) := by
  induction d generalizing offset tree with
  | zero =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have huL : ((List.range 32).map (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0)).sum = upper := by
        simpa using (Bool.and_eq_true_iff.mp hh).2
      have hu : (∑ k ∈ Finset.range 32,
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) = upper := by
        rw [← huL]
        have hset : (List.range 32).toFinset = Finset.range 32 := by
          ext k
          simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
        simpa only [hset] using List.sum_toFinset (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) (List.nodup_range (n := 32))
      have huR : (∑ k ∈ Finset.range 32,
          if offset + k < B then (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ)
          else 0) = (upper : ℝ) := by exact_mod_cast hu
      simp only [pow_zero, mul_one, mobiusHarmonicUpper]
      calc
        _ ≤ (∑ k ∈ Finset.range 32,
            if offset + k < B then
              (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ) else 0) / (Q : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum
          intro k hk
          by_cases hkB : offset + k < B
          · simp only [if_pos hkB]
            exact mobiusHarmonicCeil_bound Q (offset + k) (M (offset + k)) hQ
          · simp [hkB]
        _ = _ := by rw [huR]
  | succ d ih =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan, Finset.sum_range_add]
      have hl := ih offset l hh.1
      have hr := ih (offset + 32 * 2 ^ d) r hh.2.1
      have hr' : (∑ k ∈ Finset.range (32 * 2 ^ d),
          if offset + (32 * 2 ^ d + k) < B then
            |(M (offset + (32 * 2 ^ d + k)) : ℝ)| / (offset + (32 * 2 ^ d + k) : ℕ)
          else 0) ≤ (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := by
        simpa [Nat.add_assoc] using hr
      calc
        _ ≤ (mobiusHarmonicUpper l : ℝ) / (Q : ℝ) +
            (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := add_le_add hl hr'
        _ = _ := by simp only [mobiusHarmonicUpper, hh.2.2, Nat.cast_add, add_div]

theorem moebius_finite_harmonic_certificate (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∑ n ∈ Finset.Ico 1 B,
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ)) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) := by
  let g := mobiusTreeValue dm muTree
  let M := mobiusPrefixValue dh hTree
  have hg : ∀ n < B, g n = moebius n := mobiusTreeCheck_sound B dm muTree hB hmCapacity hm
  have hp : ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
    apply prefix_of_local_checks g M B
    intro n hn
    exact mobiusHarmonicTreeCheck_local_sound g M Q B dh 0 hTree hh n (Nat.zero_le _)
      (by simpa using lt_of_lt_of_le hn hhCapacity) hn
  have hM (n : ℕ) (hn : n < B) :
      (M n : ℝ) = ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) := by
    have ht : M n = ∑ d ∈ Finset.range (n + 1), moebius d := by
      rw [hp n hn]
      apply Finset.sum_congr rfl
      intro d hd
      exact hg d (by have h := Finset.mem_range.mp hd; omega)
    rw [Finset.sum_range_eq_add_Ico (fun d => moebius d) (Nat.zero_lt_succ n),
      ArithmeticFunction.map_zero, zero_add] at ht
    simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at ht
    exact_mod_cast ht
  have hb := mobiusHarmonicTreeCheck_bound g M Q B dh 0 hTree hQ hh
  simp only [zero_add] at hb
  have heq : (∑ n ∈ Finset.range (32 * 2 ^ dh),
      if n < B then |(M n : ℝ)| / (n : ℝ) else 0) =
      ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
    symm
    calc
      _ = ∑ n ∈ Finset.range B, if n < B then |(M n : ℝ)| / (n : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (Finset.mem_range.mp hn)]
      _ = _ := Finset.sum_subset (Finset.range_mono hhCapacity) (by
        intro n hn hnB
        rw [if_neg (by simpa only [Finset.mem_range] using hnB)])
  rw [heq] at hb
  calc
    _ = ∑ n ∈ Finset.Ico 1 B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hM n (Finset.mem_Ico.mp hn).2]
    _ = ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_subset (by intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at *; omega)
      intro n hn hnI
      have hnB := Finset.mem_range.mp hn
      have hn0 : n = 0 := by simp only [Finset.mem_Ico] at hnI; omega
      simp [hn0]
    _ ≤ _ := hb

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma moebius_abs_summatory_single_interval (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (n : ℝ)..(n + 1 : ℕ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    _ = ∫ t in (n : ℝ)..(n + 1 : ℕ),
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| * t⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast Nat.le_succ n)
      intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by
        exact_mod_cast ht.2⟩
      dsimp only
      rw [hf]
      simp only [div_eq_mul_inv]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hnp hsucc]

theorem moebius_finite_initial_integral_certificate (B : ℕ) (hB : 1 ≤ B) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      (∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
          Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) ∧
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      ∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ) := by
  have hi (n : ℕ) (hn : n ∈ Finset.Ico 1 B) :
      IntervalIntegrable (fun t : ℝ =>
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t)
        volume (n : ℝ) (n + 1 : ℕ) := by
    have hn1 := (Finset.mem_Ico.mp hn).1
    have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    have hb : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (n : ℝ) (n + 1 : ℕ) := by
      apply intervalIntegral.intervalIntegrable_inv (f := fun t : ℝ => t)
      · intro t ht
        simp only [Set.uIcc_of_le hle, Set.mem_Icc] at ht
        exact (hnp.trans_le ht.1).ne'
      · exact continuous_id.continuousOn
    apply (hb.const_mul |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)|).congr_uIoo
    intro t ht
    simp only [Set.uIoo_of_le hle, Set.mem_Ioo] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by exact_mod_cast ht.2⟩
    dsimp only
    rw [hf]
    simp only [div_eq_mul_inv]
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ))
    hB (fun n hn => hi n (Finset.mem_Ico.mpr hn))
  simp only [Nat.cast_one] at hs
  have hid :
      (∫ t in (1 : ℝ)..(B : ℝ),
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
        ∑ n ∈ Finset.Ico 1 B,
          |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
            Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro n hn
    exact moebius_abs_summatory_single_interval n (Finset.mem_Ico.mp hn).1
  refine ⟨hid, ?_⟩
  rw [hid]
  apply Finset.sum_le_sum
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by have h := (Finset.mem_Ico.mp hn).1; omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hnp)
  calc
    _ ≤ |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        (((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ = _ := by push_cast; field_simp; ring

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_initial_integral_of_finite_certificate_complete (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) :=
  (moebius_finite_initial_integral_certificate B hBpos).2.trans
    (moebius_finite_harmonic_certificate B dm dh Q muTree hTree hB hmCapacity hhCapacity hQ hm hh)

end Helfgott
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators
namespace Helfgott

lemma reciprocal_integer_rounding_error (Q n : ℕ) (a : ℤ)
    (hQ : 0 < Q) (hn : 0 < n) (ha : |a| ≤ 1) :
    |(a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| ≤
      1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have har : |(a : ℝ)| ≤ 1 := by exact_mod_cast ha
  have hf : |(Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)| ≤ 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.abs_sub_floor_le (a := (Q : ℝ) / (n : ℝ)) (by positivity))
  have he : (a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ) =
      (a : ℝ) * ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)) / (Q : ℝ) := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hQr]
  exact div_le_div_of_nonneg_right
    (by nlinarith [abs_nonneg (a : ℝ), abs_nonneg ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ))]) hQr.le

theorem moebius_reciprocal_rounded_sum_error (Q N : ℕ) (hQ : 0 < Q) :
    |(∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ)| ≤
      (N : ℝ) / (Q : ℝ) := by
  have he : (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ) =
      ∑ n ∈ Finset.Icc 1 N,
        (((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_integer_rounding_error Q n (moebius n) hQ
        (by have := (Finset.mem_Icc.mp hn).1; omega) abs_moebius_le_one
    _ = (N : ℝ) / (Q : ℝ) := by simp [Nat.card_Icc, div_eq_mul_inv]

theorem moebius_reciprocal_of_rounded_sum (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) :
    |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he := moebius_reciprocal_rounded_sum_error Q N hQ
  rw [← hS] at he
  have ht := abs_add_le
    ((∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) - (S : ℝ) / (Q : ℝ))
    ((S : ℝ) / (Q : ℝ))
  rw [sub_add_cancel, abs_div, abs_of_pos hQr] at ht
  have habs : |(S : ℝ)| = (S.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [habs] at ht
  exact ht.trans (by rw [add_div]; linarith [he])

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators
namespace Helfgott

theorem moebius_reciprocal_log_decay_of_integer_certificate
    (Q N L : ℕ) (S : ℤ) (x : ℝ)
    (hQ : 0 < Q) (hN : 2 ≤ N) (hx : (N : ℝ) ≤ x) (hxnext : x < N + 1)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ))
    (hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ (L : ℝ) / 10)
    (hnum : 10 * (S.natAbs + N) * L ≤ 3 * Q) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100 : ℝ) / Real.log x := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hxpos : 0 < x := by linarith
  have hxone : 1 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hxone
  have hfloor : ⌊x⌋₊ = N := (Nat.floor_eq_iff hxpos.le).mpr ⟨hx, hxnext⟩
  rw [hfloor]
  have hbound := moebius_reciprocal_of_rounded_sum Q N S hQ hS
  have hxlog : Real.log x ≤ (L : ℝ) / 10 := by
    apply le_trans (Real.log_le_log hxpos (by exact_mod_cast hxnext.le)) hlog
  have hnumr : 10 * ((S.natAbs : ℝ) + (N : ℝ)) * (L : ℝ) ≤ 3 * (Q : ℝ) := by
    exact_mod_cast hnum
  apply (le_div_iff₀ hlogpos).mpr
  calc
    _ ≤ (((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ)) * Real.log x :=
      mul_le_mul_of_nonneg_right hbound hlogpos.le
    _ ≤ (((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ)) * ((L : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left hxlog (by positivity)
    _ ≤ 3 / 100 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mpr
      rw [show ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) * ((L : ℝ) / 10) * 100 =
        (10 * ((S.natAbs : ℝ) + (N : ℝ)) * (L : ℝ)) / (Q : ℝ) by ring]
      exact (div_le_iff₀ hQr).mpr hnumr

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators
namespace Helfgott

lemma mobiusRoundedPrefix_eq_moebius_Icc (g : ℕ → ℤ) (Q N B : ℕ)
    (hN : N < B) (hg : ∀ n < B, g n = moebius n) :
    mobiusRoundedPrefix g Q (N + 1) =
      ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ) := by
  have hsubset : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  have hsum : (∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) =
      ∑ n ∈ Finset.range (N + 1), (moebius n : ℤ) * (Q / n : ℕ) := by
    apply Finset.sum_subset hsubset
    intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Icc, not_and_or] at hnot
      omega
    simp [hn0]
  rw [hsum, mobiusRoundedPrefix]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hg n (by have := Finset.mem_range.mp hn; omega)]

theorem moebius_reciprocal_decay_of_finite_certificate_complete
    (A B Q dm dr : ℕ) (muTree : MobiusCertTree) (rTree : MobiusReciprocalTree)
    (hA : 2 ≤ A) (hB : B ≤ 1200001) (hQ : 0 < Q)
    (hmCapacity : B ≤ 32 * 2 ^ dm) (hrCapacity : B ≤ 32 * 2 ^ dr)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hstart : mobiusReciprocalStart rTree = 0)
    (hr : mobiusReciprocalTreeCheck (mobiusTreeValue dm muTree) Q A B dr 0 rTree = true) :
    ∀ x : ℝ, (A : ℝ) ≤ x → x < (B : ℝ) →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
        (3 / 100 : ℝ) / Real.log x := by
  intro x hxA hxB
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hx0 : 0 ≤ x := by linarith
  let N := ⌊x⌋₊
  have hAN : A ≤ N := Nat.le_floor hxA
  have hNB : N < B := (Nat.floor_lt hx0).mpr hxB
  have hg := mobiusTreeCheck_sound B dm muTree hB hmCapacity hm
  have hs : mobiusReciprocalStart rTree =
      mobiusRoundedPrefix (mobiusTreeValue dm muTree) Q (min B 0) := by
    simpa only [Nat.min_zero, mobiusRoundedPrefix, Finset.range_zero, Finset.sum_empty] using hstart
  obtain ⟨K, hnum, hlog⟩ := mobiusReciprocalTree_integer_bounds
    (mobiusTreeValue dm muTree) Q A B dr 0 rTree hs hr N (Nat.zero_le N)
      (by simpa only [zero_add] using lt_of_lt_of_le hNB hrCapacity) hAN hNB
  have hS := mobiusRoundedPrefix_eq_moebius_Icc (mobiusTreeValue dm muTree) Q N B hNB hg
  exact moebius_reciprocal_log_decay_of_integer_certificate Q N K
    (mobiusRoundedPrefix (mobiusTreeValue dm muTree) Q (N + 1)) x hQ (hA.trans hAN)
    (Nat.floor_le hx0) (Nat.lt_floor_add_one x) hS hlog hnum

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators

theorem solution 
    (A B Q dm dr : ℕ) (muTree : MobiusCertTree) (rTree : MobiusReciprocalTree)
    (hA : 2 ≤ A) (hB : B ≤ 1200001) (hQ : 0 < Q)
    (hmCapacity : B ≤ 32 * 2 ^ dm) (hrCapacity : B ≤ 32 * 2 ^ dr)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hstart : mobiusReciprocalStart rTree = 0)
    (hr : mobiusReciprocalTreeCheck (mobiusTreeValue dm muTree) Q A B dr 0 rTree = true) :
    ∀ x : ℝ, (A : ℝ) ≤ x → x < (B : ℝ) →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
        (3 / 100 : ℝ) / Real.log x := Helfgott.moebius_reciprocal_decay_of_finite_certificate_complete A B Q dm dr muTree rTree hA hB hQ hmCapacity hrCapacity hm hstart hr

#print axioms solution
