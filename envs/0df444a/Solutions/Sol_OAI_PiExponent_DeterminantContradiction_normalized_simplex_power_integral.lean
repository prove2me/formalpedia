-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.normalized_simplex_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:03:31.936646+00:00
-- url     : https://prove2.me/submissions/3117b886-7e40-4733-a0a6-e0c78d4b4523

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic

theorem solution (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ∫ t in (0 : ℝ)..U, (U - t) ^ m / (Nat.factorial m : ℝ) =
      (U ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ) := by
  rw [intervalIntegral.integral_div]
  have hreflection : (∫ t in (0 : ℝ)..U, (U - t) ^ m) =
      ∫ t in (0 : ℝ)..U, t ^ m := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := U)
        (fun t : ℝ => t ^ m) U)
  rw [hreflection, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero m), sub_zero, div_div,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
