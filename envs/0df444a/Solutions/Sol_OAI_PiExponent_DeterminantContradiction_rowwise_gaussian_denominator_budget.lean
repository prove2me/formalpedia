-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:17:31.572036+00:00
-- url     : https://prove2.me/submissions/61879027-04c0-49dd-ab3d-1b94e002056d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_rowwise_gaussian_denominator_budget_row_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_rowwise_gaussian_denominator_budget_sum_rows

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H) :
    ∃ scale : Row d H → Nat,
      (∀ ρ, 0 < scale ρ) ∧
      (∀ ρ σ, ∃ a b : Int,
        (scale ρ : Complex) * (actualMinor d H selection) ρ σ =
          (a : Complex) + Complex.I * (b : Complex)) ∧
      (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
        ((actualRowCount d H : Real) * H) *
          (1 - actualMean d H + d.arithmeticError) := by
  obtain ⟨scale, hpos, hgauss, hrow⟩ :=
    OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_row_bound
      d H hH selection
  refine ⟨scale, hpos, hgauss, ?_⟩
  exact OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_sum_rows
    d H hH scale hrow