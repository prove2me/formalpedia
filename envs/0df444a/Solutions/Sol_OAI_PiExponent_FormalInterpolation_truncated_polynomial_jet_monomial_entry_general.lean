-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_monomial_entry_general
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:28:35.680105+00:00
-- url     : https://prove2.me/submissions/181037df-f073-4e41-8d20-fbc09b6b122e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_split_jet_monomial_flattened_product
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (j : Nat) (r : Fin m → Complex)
    (G : Fin m → Polynomial Complex)
    (e a : Fin (m + 1) → Nat) :
    (MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
        Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector a) =
      InterpolationMatrix.entry r G j (a 0) (fun i => a i.succ)
        (e 0) (fun i => e i.succ) := by
  exact (congrArg
    (fun P : MvPolynomial (Fin (m + 1)) Complex =>
      P.coeff (InterpolationMatrix.exponentVector a))
    (split_jet_monomial_flattened_product j r G e)).trans
      (flattened_coeff
        (InterpolationMatrix.monomialImage r G j (e 0) (fun i => e i.succ)) a)
