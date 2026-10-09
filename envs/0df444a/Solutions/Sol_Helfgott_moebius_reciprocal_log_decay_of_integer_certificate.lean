-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_log_decay_of_integer_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:52:37.139455+00:00
-- url     : https://prove2.me/submissions/70be81a6-9733-45ff-ae94-5e9a15233d0e

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

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

theorem moebius_reciprocal_log_decay_of_integer_certificate_complete
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

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators
theorem solution 
    (Q N L : ℕ) (S : ℤ) (x : ℝ)
    (hQ : 0 < Q) (hN : 2 ≤ N) (hx : (N : ℝ) ≤ x) (hxnext : x < N + 1)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ))
    (hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ (L : ℝ) / 10)
    (hnum : 10 * (S.natAbs + N) * L ≤ 3 * Q) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100 : ℝ) / Real.log x := Helfgott.moebius_reciprocal_log_decay_of_integer_certificate_complete Q N L S x hQ hN hx hxnext hS hlog hnum
#print axioms solution
