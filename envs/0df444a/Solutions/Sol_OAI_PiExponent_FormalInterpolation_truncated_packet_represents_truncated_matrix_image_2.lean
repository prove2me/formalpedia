-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.truncated_packet_represents_truncated_matrix_image
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:07:05.515979+00:00
-- url     : https://prove2.me/submissions/96443456-9582-45e4-9631-26a49f931cd1

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_is_column_monomial_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (x : InterpolationMatrix.Column d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val =
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T).mulVecLin x := by
  classical
  obtain ⟨Q, hQ⟩ := OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
    (m := d.m) d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H x
  have hcols : ∀ a ∈ Q.val.support, ∃ c : InterpolationMatrix.Column d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      InterpolationMatrix.exponentVector c.1 = a := by
    intro a ha
    by_contra h
    simp only [not_exists] at h
    have hzero : Q.val.coeff a = 0 := by
      rw [hQ, MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      rw [MvPolynomial.coeff_monomial]
      simp [h c]
    rw [MvPolynomial.mem_support_iff] at ha
    exact ha hzero
  refine ⟨Q, ?_⟩
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
    d.K d.w0 d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val hcols]
  congr 1
  funext c
  rw [hQ, MvPolynomial.coeff_sum]
  refine (Finset.sum_eq_single c ?_ ?_).trans ?_
  · intro c' _ hne
    rw [MvPolynomial.coeff_monomial]
    have hne' : InterpolationMatrix.exponentVector c'.1 ≠
        InterpolationMatrix.exponentVector c.1 := by
      intro heq
      exact hne (Subtype.ext (Finsupp.equivFunOnFinite.symm.injective heq))
    simp [hne']
  · intro hc
    exact absurd (Finset.mem_univ c) hc
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
