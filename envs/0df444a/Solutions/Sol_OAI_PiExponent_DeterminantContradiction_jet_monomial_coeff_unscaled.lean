-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_unscaled
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:58:07.742592+00:00
-- url     : https://prove2.me/submissions/0bc3dec1-b7c6-424e-9325-201408444d93

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_general_complex
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (m : Nat) (r : Fin m -> Complex) (T : Fin m -> Nat)
    (j h : Nat) (a b : Fin m -> Nat) (s : Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by
  simpa [truncatedPolynomialJet, InterpolationMatrix.monomialImage] using
    OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_general_complex
      m (fun i => (j : Complex) * r i)
      (fun i => InterpolationMatrix.truncatedLog (T i)) h a s b