-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.restrict_row_budget_to_minor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:28:31.116819+00:00
-- url     : https://prove2.me/submissions/610d565b-b572-4c52-ae4f-b4d0720079c0

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hfull : ∃ scale : Row d H → Nat,
      (∀ ρ, 0 < scale ρ) ∧
      (∀ ρ c, ∃ a b : Int,
        (scale ρ : Complex) * (actualMatrix d H) ρ c =
          (a : Complex) + Complex.I * (b : Complex)) ∧
      (∀ ρ : Row d H,
        Real.log (scale ρ : Real) ≤
          H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
            MatrixArithmetic.logWeights (finiteDenominators d) i) +
            H * d.arithmeticError)) :
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
  rcases hfull with ⟨scale, hpos, hentry, hbudget⟩
  refine ⟨scale, hpos, ?_, hbudget⟩
  intro ρ σ
  obtain ⟨a, b, hab⟩ := hentry ρ (selection σ)
  refine ⟨a, b, ?_⟩
  simpa [actualMinor, MatrixArithmetic.selectedMinor, actualMatrix] using hab