-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_polynomial_realizes_column_coefficients_for_truncated_image
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:48:28.467543+00:00
-- url     : https://prove2.me/submissions/2af81a71-7d55-41df-8963-9682bd81f04a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_image_finite_monomial_polynomial
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_image_support_is_weight_bounded

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      ∀ c : InterpolationMatrix.Column w0 w H,
        Q.val.coeff (InterpolationMatrix.exponentVector c.1) = x c := by
  obtain ⟨P, hcoeff, hsupp⟩ :=
    OAI.PiExponent.FormalInterpolation.truncated_image_finite_monomial_polynomial
      w0 w H x
  refine ⟨⟨P,
    OAI.PiExponent.FormalInterpolation.truncated_image_support_is_weight_bounded
      w0 w H P hsupp⟩, ?_⟩
  exact hcoeff
