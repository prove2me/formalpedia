-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:11:33.793439+00:00
-- url     : https://prove2.me/submissions/fdc8aa7e-0109-4908-8ba9-afaa4d7d4f6d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 <= r) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r))
      (fun t : Real => (r - t) ^ n / (Nat.factorial n : Real)) =
      r ^ (n + 1) / (Nat.factorial (n + 1) : Real) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hr]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : Real => x ^ n) r]
  rw [integral_pow]
  simp only [sub_self, zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [div_div, Nat.factorial_succ]
  push_cast
  rfl