-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_row_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:21:43.577274+00:00
-- url     : https://prove2.me/submissions/c79771d9-acbd-4b7c-b13e-102bb80f30f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_full_matrix_row_gaussian_denominator_budget
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_restrict_row_budget_to_minor

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H) :
    ∃ scale : Row d H → Nat,
      (∀ ρ, 0 < scale ρ) ∧
      (∀ ρ σ, ∃ a b : Int,
        (scale ρ : Complex) * (actualMinor d H selection) ρ σ =
          (a : Complex) + Complex.I * (b : Complex)) ∧
      (∀ ρ : Row d H,
        Real.log (scale ρ : Real) ≤
          H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
            MatrixArithmetic.logWeights (finiteDenominators d) i) +
            H * d.arithmeticError) := by
  exact OAI.PiExponent.DeterminantContradiction.restrict_row_budget_to_minor
    d H hH selection
    (OAI.PiExponent.DeterminantContradiction.full_matrix_row_gaussian_denominator_budget
      d H hH)