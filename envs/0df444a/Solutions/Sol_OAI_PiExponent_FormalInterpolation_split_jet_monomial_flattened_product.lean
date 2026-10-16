-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.split_jet_monomial_flattened_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:37:12.633393+00:00
-- url     : https://prove2.me/submissions/2e59b1dc-2428-467f-8dad-f59c8233ddf7

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (j : Nat) (r : Fin m → Complex)
    (G : Fin m → Polynomial Complex)
    (e : Fin (m + 1) → Nat) :
    MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
        Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) (1 : Complex)) =
    MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ)
      (MvPolynomial.C ((1 + Polynomial.X) ^ e 0) *
        ∏ i, (MvPolynomial.C (Polynomial.C ((j : Complex) * r i) + G i) +
          MvPolynomial.X i) ^ e i.succ) := by
  classical
  simp [MvPolynomial.aeval_monomial, InterpolationMatrix.exponentVector,
    Polynomial.aeval_def, Fin.prod_univ_succ,
    add_assoc, add_comm, add_left_comm]