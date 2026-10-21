-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:13:51.92647+00:00
-- url     : https://prove2.me/submissions/3c62419c-5ba1-4818-b5cf-8f86a85ba48f

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion_monomial

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (j : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T P).coeff
        (InterpolationMatrix.exponentVector a) =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          j (a 0) (fun i => a i.succ) (e 0) (fun i => e i.succ) := by
  classical
  rw [OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_support]
  apply Finset.sum_congr rfl
  intro e he
  have hexp : InterpolationMatrix.exponentVector (fun i => e i) = e := by
    exact Finsupp.equivFunOnFinite_symm_coe e
  have hmono :=
    OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion_monomial
      j r T (fun i => e i) a
  rw [hexp] at hmono
  exact congrArg (fun z : Complex => P.coeff e * z) hmono