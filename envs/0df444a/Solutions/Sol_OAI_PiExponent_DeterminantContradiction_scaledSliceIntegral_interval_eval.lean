-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_interval_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:37:50.736617+00:00
-- url     : https://prove2.me/submissions/7ac006ef-6323-4cfe-88d9-2375a2a08ac4

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n = ((n : ℝ) + 1)⁻¹ := by
  calc
    (∫ t in (0 : ℝ)..1, (1 - t) ^ n) = ∫ t in (0 : ℝ)..1, t ^ n := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t : ℝ => t ^ n) (1 : ℝ))
    _ = ((n : ℝ) + 1)⁻¹ := by
      simpa using (integral_pow (a := (0 : ℝ)) (b := (1 : ℝ)) n)
