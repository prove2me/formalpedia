-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:47:40.011614+00:00
-- url     : https://prove2.me/submissions/d2707ada-6c9a-4569-a59c-d6abb42670c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monic_relations_of_bounded_representatives
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_bounded_representatives

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
  obtain ⟨rho, B, hrho0, hrhoR, hB, hbound⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_representatives
      d R S e T hR hRS he hcommon hcapacity hT
  have hw : ∀ i : Fin (d.m + 1), 0 < InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [InterpolationMatrix.columnWeights, Fin.cases_zero]
      exact d.w0_pos
    · intro j
      simp only [InterpolationMatrix.columnWeights, Fin.cases_succ]
      have hq2 : (2 : ℕ) ≤ (finiteDenominators d) j := (d.approximations j.val).1
      have h1 : (1 : ℝ) < ((finiteDenominators d) j : ℝ) := by
        have h2 : (1 : ℕ) < (finiteDenominators d) j := by omega
        exact_mod_cast h2
      have h3 : (0 : ℕ) < ⌈Real.log ((finiteDenominators d) j)⌉₊ :=
        Nat.ceil_pos.mpr (Real.log_pos h1)
      unfold MatrixArithmetic.logWeights
      exact_mod_cast h3
  exact OAI.PiExponent.LogarithmicJetIdeals.monic_relations_of_bounded_representatives
    (w := fun i => InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i) hw
    (simultaneousJetIdeal d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T e)
    R rho B hrho0 hrhoR hB (by
      intro k hk P
      exact hbound k hk P)
