-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_worker_2de3db86_a846_49cd_be11_af72b2b621e1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:11.559182+00:00
-- url     : https://prove2.me/submissions/47430c5a-dcc9-4f28-9c2d-f0d635e65a10

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j s h : Nat) (b a : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by
  apply OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1 <;> assumption
