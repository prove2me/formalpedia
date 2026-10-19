-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:45:25.33681+00:00
-- url     : https://prove2.me/submissions/051a4fc0-7a73-4421-8d7c-3454adbbba90

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_slicing_integral

open scoped BigOperators

theorem solution (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      1 / (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      simp [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
      have hint : (∫ t in (0 : ℝ)..1, (1 - t) ^ n) =
          1 / ((n + 1 : ℕ) : ℝ) := by
        calc
          (∫ t in (0 : ℝ)..1, (1 - t) ^ n) =
              ∫ t in (1 - 1 : ℝ)..(1 - 0 : ℝ), t ^ n :=
            intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) 1
          _ = 1 / ((n + 1 : ℕ) : ℝ) := by simp
      rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing_integral
        n 1 zero_lt_one, ih, hint, Nat.factorial_succ, Nat.cast_mul]
      simp only [one_div, mul_inv_rev]
