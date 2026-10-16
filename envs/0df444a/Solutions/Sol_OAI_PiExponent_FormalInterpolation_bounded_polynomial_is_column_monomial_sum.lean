-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:54:56.47127+00:00
-- url     : https://prove2.me/submissions/e6e2f458-0231-4f63-bab1-c243dd558986

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      Q.val = ∑ c : InterpolationMatrix.Column w0 w H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c) := by
  classical
  let p : MvPolynomial (Fin (m + 1)) Complex :=
    ∑ c : InterpolationMatrix.Column w0 w H,
      MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)
  refine ⟨⟨p, ?_⟩, ?_⟩
  · intro a ha
    have hsum := MvPolynomial.support_sum
      (s := (Finset.univ : Finset (InterpolationMatrix.Column w0 w H)))
      (f := fun c => MvPolynomial.monomial
        (InterpolationMatrix.exponentVector c.1) (x c))
    have ha' : a ∈ (Finset.univ : Finset (InterpolationMatrix.Column w0 w H)).biUnion
        (fun c => (MvPolynomial.monomial
          (InterpolationMatrix.exponentVector c.1) (x c)).support) := by
      simpa [p] using hsum ha
    rcases Finset.mem_biUnion.mp ha' with ⟨c, -, hmon⟩
    have hsubset := MvPolynomial.support_monomial_subset
      (s := InterpolationMatrix.exponentVector c.1) (a := x c)
    have hEq : a = InterpolationMatrix.exponentVector c.1 := by
      simpa using hsubset hmon
    subst a
    have hc : c.1 ∈ OAI.PiExponent.realWeightedSimplex
        (InterpolationMatrix.columnWeights w0 w) H := c.2
    change c.1 ∈ (Fintype.piFinset
      (fun i => Finset.range (⌊H / InterpolationMatrix.columnWeights w0 w i⌋₊ + 1))).filter
      (fun a => ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H) at hc
    have hweight := (Finset.mem_filter.mp hc).2
    simpa [InterpolationMatrix.exponentVector] using hweight
  · rfl
