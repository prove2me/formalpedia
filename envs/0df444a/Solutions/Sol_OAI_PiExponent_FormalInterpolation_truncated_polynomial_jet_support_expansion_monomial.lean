-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:17:30.334382+00:00
-- url     : https://prove2.me/submissions/fa2389de-cb89-4d6e-8236-40b09e40afad

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_monomial_entry_general

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (e a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector a) =
      InterpolationMatrix.entry
        r (fun i => InterpolationMatrix.truncatedLog (T i))
        j (a 0) (fun i => a i.succ) (e 0) (fun i => e i.succ) := by
  simpa [truncatedPolynomialJet] using
    OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_monomial_entry_general
      j r (fun i => InterpolationMatrix.truncatedLog (T i)) e a