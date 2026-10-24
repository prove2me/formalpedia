-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_surjective_weighted_monomial_sum_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:28:01.087537+00:00
-- url     : https://prove2.me/submissions/45395478-299a-45a9-8a02-d34ef4f870ef

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 =
        ∑ c : Column d H,
          MvPolynomial.C (a c) *
            MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1 := by
  classical
  let f : Column d H → MvPolynomial (Fin (d.m + 1)) Complex := fun c =>
    MvPolynomial.C (a c) *
      MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1
  let S : MvPolynomial (Fin (d.m + 1)) Complex := ∑ c : Column d H, f c
  refine ⟨⟨S, ?_⟩, ?_⟩
  · intro e he
    have heCoeff : (∑ c : Column d H, f c).coeff e ≠ 0 := by
      change e ∈ (∑ c : Column d H, f c).support at he
      simpa only [MvPolynomial.mem_support_iff] using he
    have hex : ∃ c : Column d H, (f c).coeff e ≠ 0 := by
      by_contra h
      apply heCoeff
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro c hc
      have hzero : (f c).coeff e = 0 := by
        by_contra hne
        exact h ⟨c, hne⟩
      exact hzero
    obtain ⟨c, hc⟩ := hex
    have heMono : e = InterpolationMatrix.exponentVector c.1 := by
      have hc' :
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (a c)).coeff e ≠ 0 := by
        simpa [f, MvPolynomial.C_mul_monomial] using hc
      by_contra hne
      have hneq : InterpolationMatrix.exponentVector c.1 ≠ e := fun h' => hne h'.symm
      simp [MvPolynomial.coeff_monomial, hneq] at hc'
    subst e
    have hbound :
        ∑ i, InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) i *
            (c.1 i : Real) ≤ H := by
      have hmem :
          c.1 ∈ realWeightedSimplex
            (InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d))) H := c.2
      simp only [realWeightedSimplex, Finset.mem_filter] at hmem
      exact hmem.2
    simpa [InterpolationMatrix.exponentVector,
      InterpolationMatrix.columnWeights] using hbound
  · rfl
