-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:31:59.461558+00:00
-- url     : https://prove2.me/submissions/dfc36cc6-05dc-4961-9211-54935b331fba

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_slice_integral_repair4

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / (n + 1 : Real) := by
  apply OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral_repair4 <;> assumption
