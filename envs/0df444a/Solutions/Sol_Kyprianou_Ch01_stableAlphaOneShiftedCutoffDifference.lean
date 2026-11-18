-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneShiftedCutoffDifference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:26:28.395026+00:00
-- url     : https://prove2.me/submissions/0ff18a31-9037-41be-9e11-54e9df181e3f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The cutoff change cancels sine terms and is exactly an inverse kernel. -/
theorem solution
    (z u : ℝ) :
    ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) -
      ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) =
        ((if u < z then (1 : ℝ) else 0) -
          (if u < 1 then (1 : ℝ) else 0)) / u := by
  by_cases hu : u = 0
  · subst u
    simp
  · field_simp
    ring
