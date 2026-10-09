-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_of_rounded_sum
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:38:17.885878+00:00
-- url     : https://prove2.me/submissions/bf7001f5-d7c5-4d99-a2a4-995bd5a745e6

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

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

theorem moebius_reciprocal_of_rounded_sum_complete (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
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

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators

theorem solution  (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) :
    |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) := Helfgott.moebius_reciprocal_of_rounded_sum_complete Q N S hQ hS

#print axioms solution
