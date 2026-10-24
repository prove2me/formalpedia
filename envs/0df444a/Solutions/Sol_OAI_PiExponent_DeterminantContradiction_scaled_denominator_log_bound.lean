-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaled_denominator_log_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:10:16.738417+00:00
-- url     : https://prove2.me/submissions/387d5e84-169d-4e65-9deb-4a6bd6020862
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_rowwise_gaussian_denominator_budget
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_det_of_rowwise_gaussian_integrality

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    ∃ D : Nat, 0 < D ∧
      ∃ a b : Int,
        (D : Complex) * (actualMinor d H selection).det =
            (a : Complex) + Complex.I * (b : Complex) ∧
          Real.log (D : Real) ≤
            ((actualRowCount d H : Real) * H) *
              (1 - actualMean d H + d.arithmeticError) := by
  obtain ⟨scale, hscale_pos, hscale_int, hbudget⟩ :=
    OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget
      d H hH selection
  exact OAI.PiExponent.DeterminantContradiction.det_of_rowwise_gaussian_integrality
    (actualMinor d H selection) scale hscale_pos hscale_int
    (((actualRowCount d H : Real) * H) *
      (1 - actualMean d H + d.arithmeticError)) hbudget