-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_integral_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:56:02.056957+00:00
-- url     : https://prove2.me/submissions/6888daed-3587-4f1b-a97e-e1047e8b8d4f

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open intervalIntegral

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / ((n + 1 : Nat) : Real) := by
  calc
    (∫ t in (0 : Real)..1, (1 - t) ^ n) =
        ∫ x in (1 - 1 : Real)..(1 - 0), x ^ n := by
      simpa using
        (intervalIntegral.integral_comp_sub_left (f := fun x : Real => x ^ n)
          (a := (0 : Real)) (b := 1) (d := 1))
    _ = 1 / ((n + 1 : Nat) : Real) := by
      rw [integral_pow]
      norm_num