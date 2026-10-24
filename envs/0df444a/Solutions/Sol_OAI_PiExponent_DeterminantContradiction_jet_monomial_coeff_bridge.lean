-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:45:42.01648+00:00
-- url     : https://prove2.me/submissions/da3e7bbe-f643-4c7f-9ecc-9628caeb6cb0

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_unscaled
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    (m : Nat) (r : Fin m -> Complex) (T : Fin m -> Nat)
    (j h : Nat) (a b : Fin m -> Nat) (s : Nat) (z : Complex) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.C z *
        MvPolynomial.monomial
          (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    z * ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by
  classical
  calc
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.C z *
        MvPolynomial.monomial
          (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      z * (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
        (MvPolynomial.monomial
          (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
          (InterpolationMatrix.exponentVector (Fin.cases s b)) := by
      simp only [truncatedPolynomialJet, map_mul, MvPolynomial.aeval_C]
      exact MvPolynomial.coeff_C_mul _ _ _
    _ = z * ((InterpolationMatrix.monomialImage r
        (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
        (InterpolationMatrix.exponentVector b)).coeff s := by
      rw [OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_unscaled]