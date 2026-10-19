-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:35:16.417346+00:00
-- url     : https://prove2.me/submissions/ea67134c-03dd-4edd-9f63-7d5abea78ed3

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity

open scoped BigOperators

theorem solution
    (m : ℕ)
    (hprev : ∀ (V : ℝ), 0 ≤ V →
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ V}).toReal =
        V ^ m / (Nat.factorial m : ℝ))
    (U : ℝ) (hU : 0 ≤ U) :
    ∫ t in (0 : ℝ)..U,
      (MeasureTheory.volume
        {x : Fin m → ℝ |
          (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal =
      U ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
  have hpow : ∫ x in (0 : ℝ)..U, x ^ m = U ^ (m + 1) / (m + 1 : ℝ) := by
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) U,
        HasDerivAt (fun y : ℝ => y ^ (m + 1))
          ((m + 1 : ℝ) * x ^ m) x := by
      intro x hx
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
        (hasDerivAt_pow (m + 1) x)
    have hint : IntervalIntegrable (fun x : ℝ => (m + 1 : ℝ) * x ^ m)
        MeasureTheory.volume 0 U := by
      exact ((continuous_const : Continuous (fun _ : ℝ => (m + 1 : ℝ))).mul
        (continuous_id.pow m)).intervalIntegrable 0 U
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := U) hderiv hint
    rw [intervalIntegral.integral_const_mul] at hFTC
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    have hval : U ^ (m + 1) - (0 : ℝ) ^ (m + 1) = U ^ (m + 1) := by simp
    rw [hval] at hFTC
    apply (eq_div_iff hm).2
    simpa only [mul_comm] using hFTC
  calc
    (∫ t in (0 : ℝ)..U,
        (MeasureTheory.volume
          {x : Fin m → ℝ |
            (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal) =
        ∫ t in (0 : ℝ)..U, (U - t) ^ m / (Nat.factorial m : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) U := by
        simpa only [Set.uIcc_of_le hU] using ht
      exact hprev (U - t) (sub_nonneg.mpr ht'.2)
    _ = (∫ t in (0 : ℝ)..U, (U - t) ^ m) / (Nat.factorial m : ℝ) := by
      rw [intervalIntegral.integral_div]
    _ = (∫ x in (U - U)..(U - 0), x ^ m) / (Nat.factorial m : ℝ) := by
      rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ m) U]
    _ = (U ^ (m + 1) / (m + 1 : ℝ)) / (Nat.factorial m : ℝ) := by
      rw [sub_self, sub_zero, hpow]
    _ = U ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]
