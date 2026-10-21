-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_column_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:05:31.293433+00:00
-- url     : https://prove2.me/submissions/e7a57b69-f80b-4816-b393-f3cd62e7e772

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_is_column_monomial_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    truncatedPolynomialPacket K v0 theta w H r T
        (∑ c : InterpolationMatrix.Column w0 w H,
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by
  classical
  obtain ⟨Q, hQ⟩ := OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
    (m := m) w0 w H x
  have hcols : ∀ a ∈ Q.val.support, ∃ c : InterpolationMatrix.Column w0 w H,
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
  rw [← hQ]
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
    K w0 v0 theta w H r T Q.val hcols]
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
