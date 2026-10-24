-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:32:02.229074+00:00
-- url     : https://prove2.me/submissions/84676b3e-97dd-45c0-aee6-ba5b0fb2047c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    {m : ℕ} (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (j s h : ℕ) (b a : Fin m → ℕ) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : ℂ) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : ℂ))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by
  apply OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1 <;> assumption
