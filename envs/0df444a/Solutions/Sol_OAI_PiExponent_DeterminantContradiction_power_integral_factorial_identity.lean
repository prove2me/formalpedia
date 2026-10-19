-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.power_integral_factorial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:19:20.79991+00:00
-- url     : https://prove2.me/submissions/8590c3de-b8bd-4792-8a5c-a8fe9cddd7c3

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution (n : ℕ) (r : ℝ) :
    r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) =
      ((1 : ℝ) ^ n / (Nat.factorial n : ℝ)) *
        (∫ t in (0 : ℝ)..r, (r - t) ^ n) := by
  have hint :
      (∫ t in (0 : ℝ)..r, (r - t) ^ n) =
        r ^ (n + 1) / (n + 1 : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) r]
    simp only [sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero n)]
  rw [hint, one_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
