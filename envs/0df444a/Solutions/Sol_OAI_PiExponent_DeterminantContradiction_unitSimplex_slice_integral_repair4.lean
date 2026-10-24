-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral_repair4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:57:31.158474+00:00
-- url     : https://prove2.me/submissions/a76f8b4b-73bd-4538-a48f-2bad3980f1c0

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / (n + 1 : Real) := by
  calc
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = ∫ t in (0 : Real)..1, t ^ n := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ n)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = 1 / (n + 1 : Real) := by
      rw [integral_pow]
      simp