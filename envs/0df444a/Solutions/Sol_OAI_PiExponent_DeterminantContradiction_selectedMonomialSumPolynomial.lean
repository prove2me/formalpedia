-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:24:40.675329+00:00
-- url     : https://prove2.me/submissions/a17b98a6-87f6-4a1c-b2bc-a99da5102940

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (x : Row d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 = ∑ sigma : Row d H,
        MvPolynomial.C (x sigma) *
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector (selection sigma).1) 1 := by
  classical
  let f : Row d H → MvPolynomial (Fin (d.m + 1)) Complex := fun sigma =>
    MvPolynomial.C (x sigma) *
      MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (selection sigma).1) 1
  refine ⟨⟨∑ sigma : Row d H, f sigma, ?_⟩, ?_⟩
  · intro a ha
    have hsupport :
        a ∈ (Finset.univ.biUnion fun sigma : Row d H => (f sigma).support) := by
      apply MvPolynomial.support_sum (s := Finset.univ) (f := f)
      simpa [f] using ha
    rcases Finset.mem_biUnion.mp hsupport with ⟨sigma, -, hterm⟩
    let e := InterpolationMatrix.exponentVector (selection sigma).1
    have hterm_subset : (f sigma).support ⊆ {e} := by
      change (MvPolynomial.C (x sigma) * MvPolynomial.monomial e 1).support ⊆ {e}
      rw [MvPolynomial.C_mul_monomial]
      exact MvPolynomial.support_monomial_subset
    have haeq : a = e := by
      simpa using hterm_subset hterm
    have hbound :
        ∑ i : Fin (d.m + 1),
          InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i *
            ((selection sigma).1 i : Real) ≤ H := by
      have hm := (selection sigma).property
      simp only [realWeightedSimplex, Finset.mem_filter] at hm
      exact hm.2
    rw [haeq]
    simpa [e, InterpolationMatrix.exponentVector] using hbound
  · rfl