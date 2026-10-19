-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_content_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:10:24.609033+00:00
-- url     : https://prove2.me/submissions/6f0dd005-725e-41ca-a44c-0b3cef010fcd

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_recurrence

open scoped BigOperators

private theorem simplex_power_integral_aux (m : ℕ) (r : ℝ) :
    (∫ t in (0 : ℝ)..r, (r - t) ^ m / (Nat.factorial m : ℝ)) =
      r ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ m) r]
  simp only [sub_self, sub_zero, integral_pow,
    zero_pow (Nat.succ_ne_zero m), Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]

theorem solution (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ r}).toReal =
      r ^ m / (Nat.factorial m : ℝ) := by
  induction m generalizing r with
  | zero =>
      have hset :
          {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ r} =
            Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        constructor
        · intro i
          exact Fin.elim0 i
        · simpa using hr
      rw [hset, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ]
      simp
  | succ m ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_slice_recurrence m r hr]
      have hcongr :
          (∫ t in (0 : ℝ)..r,
            (MeasureTheory.volume
              {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ r - t}).toReal) =
          ∫ t in (0 : ℝ)..r, (r - t) ^ m / (Nat.factorial m : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) r := by
          simpa only [Set.uIcc_of_le hr] using ht
        exact ih (r - t) (sub_nonneg.mpr ht'.2)
      rw [hcongr]
      exact simplex_power_integral_aux m r
