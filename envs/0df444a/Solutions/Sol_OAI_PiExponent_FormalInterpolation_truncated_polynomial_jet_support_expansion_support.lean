-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:18:34.172354+00:00
-- url     : https://prove2.me/submissions/6b79f81f-2399-45e7-8c13-00e64e709069

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T P).coeff
        (InterpolationMatrix.exponentVector a) =
      ∑ e ∈ P.support,
        P.coeff e *
          (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
            (MvPolynomial.monomial e (1 : Complex))).coeff
            (InterpolationMatrix.exponentVector a) := by
  classical
  simp only [truncatedPolynomialJet]
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum, MvPolynomial.coeff_sum]
  simp [MvPolynomial.aeval_monomial, MvPolynomial.coeff_C_mul]