-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_polynomial_realizes_column_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:38:56.306685+00:00
-- url     : https://prove2.me/submissions/0cd6d149-f4cb-4ee6-93c7-dfef244049aa

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_column_monomial_interpolation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_column_exponent_support_is_bounded

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      ∀ c : InterpolationMatrix.Column w0 w H,
        Q.val.coeff (InterpolationMatrix.exponentVector c.1) = x c := by
  obtain ⟨P, hcoeff, hsupp⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_column_monomial_interpolation w0 w H x
  exact ⟨⟨P,
    OAI.PiExponent.FormalInterpolation.column_exponent_support_is_bounded w0 w H P hsupp⟩,
    hcoeff⟩
