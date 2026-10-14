-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_image_finite_monomial_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:55:15.338767+00:00
-- url     : https://prove2.me/submissions/6cb6fac0-e345-4fd4-bffb-79e17ad371a2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_injective_monomial_interpolation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m -> Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      And (forall c : InterpolationMatrix.Column w0 w H,
        P.coeff (InterpolationMatrix.exponentVector c.1) = x c)
      (P.support ⊆ Finset.univ.image
        fun c : InterpolationMatrix.Column w0 w H =>
          InterpolationMatrix.exponentVector c.1) := by
  classical
  apply OAI.PiExponent.FormalInterpolation.finite_injective_monomial_interpolation
    (e := fun c : InterpolationMatrix.Column w0 w H =>
      InterpolationMatrix.exponentVector c.1) (x := x)
  intro a b h
  apply Subtype.ext
  exact (Finsupp.equivFunOnFinite.symm.injective h)