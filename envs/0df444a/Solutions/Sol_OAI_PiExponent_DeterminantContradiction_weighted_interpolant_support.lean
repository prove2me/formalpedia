-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_interpolant_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:35:20.916988+00:00
-- url     : https://prove2.me/submissions/c5ff700d-a9c2-4684-8eac-8f7fa71ff634

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (f : Column d H → Complex) :
    ∀ a ∈ (∑ c : Column d H,
      MvPolynomial.C (f c) *
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1).support,
      ∑ i, InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ H := by
  classical
  intro a ha
  let term : Column d H → MvPolynomial (Fin (d.m + 1)) Complex := fun c =>
    MvPolynomial.C (f c) *
      MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1
  have hsub := MvPolynomial.support_sum (s := Finset.univ) (f := term)
  have hmem : a ∈ Finset.univ.biUnion (fun c : Column d H => (term c).support) := by
    apply hsub
    simpa [term] using ha
  obtain ⟨c, -, hterm⟩ := Finset.mem_biUnion.mp hmem
  have hmon : term c = MvPolynomial.monomial
      (InterpolationMatrix.exponentVector c.1) (f c) := by
    dsimp [term]
    rw [MvPolynomial.C_mul_monomial]
    simp
  have hexp : a = InterpolationMatrix.exponentVector c.1 := by
    have hsingle : a ∈ ({InterpolationMatrix.exponentVector c.1} : Finset (Fin (d.m + 1) →₀ ℕ)) :=
      MvPolynomial.support_monomial_subset (by simpa [hmon] using hterm)
    simpa using hsingle
  have hc : c.1 ∈ OAI.PiExponent.realWeightedSimplex
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    exact c.2
  unfold OAI.PiExponent.realWeightedSimplex at hc
  have hweight := (Finset.mem_filter.mp hc).2
  simpa [hexp, InterpolationMatrix.exponentVector] using hweight