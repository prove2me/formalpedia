-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:53:26.333316+00:00
-- url     : https://prove2.me/submissions/154bba51-7759-4b5f-8a97-e42ba76ef89c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) := by
  obtain ⟨hscale, D, hD, a, b, hscaled, hnorm, hlogdet, hlogD⟩ :=
    OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate
      d H hH selection hdet
  have hmul :
      (-(1 - actualMean d H) - d.arithmeticError) *
          ((actualRowCount d H : Real) * H) ≤
        Real.log ‖(actualMinor d H selection).det‖ := by
    calc
      (-(1 - actualMean d H) - d.arithmeticError) *
          ((actualRowCount d H : Real) * H) =
        -(((actualRowCount d H : Real) * H) *
          (1 - actualMean d H + d.arithmeticError)) := by ring
      _ ≤ Real.log ‖(actualMinor d H selection).det‖ := by
        linarith
  exact (le_div_iff₀ hscale).2 hmul