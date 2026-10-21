-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:37:58.545765+00:00
-- url     : https://prove2.me/submissions/d3381ff9-8528-4699-9c90-ceaeefe14ec3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_weighted_monic_relations_of_degrees
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_degree_budget

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ k : ℕ, 0 < k ∧ ∃ (b : Fin (d.m + 1) → ℕ), (∀ i, 0 < b i) ∧
      ∃ (F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ), ∃ a : ℝ,
        0 < a ∧ a < R ∧
        (∀ i, F i ∈ (simultaneousJetIdeal d.K
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d)) T e) ^ k) ∧
        (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) j * (u j : ℝ)) <
            InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ)) ∧
        (∀ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ) ≤
            (k : ℝ) * a) := by
  classical
  obtain ⟨k, hk, b, hb, a, ha0, haR, hbudget⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_degree_budget
      d R S e T hR hRS he hcommon hcapacity hT
  obtain ⟨F, hF, hbelow⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations_of_degrees
      d e T k hk b hb
  exact ⟨k, hk, b, hb, F, a, ha0, haR, hF, hbelow, hbudget⟩
