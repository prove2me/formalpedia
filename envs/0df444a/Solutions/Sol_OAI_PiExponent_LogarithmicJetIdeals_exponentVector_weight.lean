-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.exponentVector_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:04:20.855847+00:00
-- url     : https://prove2.me/submissions/61169411-44b0-4c57-9a0c-50123b5ccbf1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {n : ℕ} (q : Fin n → ℝ) (a : Fin n → ℕ) :
    (∑ j, q j * (InterpolationMatrix.exponentVector a j : ℝ)) =
      ∑ j, q j * (a j : ℝ) := by
  simp [InterpolationMatrix.exponentVector]