-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:59:23.778861+00:00
-- url     : https://prove2.me/submissions/c309babf-0251-4150-b618-6f30ebd124d5

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomialImage_substitution
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mapped_coeff_transport
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j s h : Nat) (b a : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by
  rw [OAI.PiExponent.FormalInterpolation.monomialImage_substitution r G j h a]
  simpa [InterpolationMatrix.entry] using
    OAI.PiExponent.FormalInterpolation.mapped_coeff_transport
      (InterpolationMatrix.monomialImage r G j h a) s b