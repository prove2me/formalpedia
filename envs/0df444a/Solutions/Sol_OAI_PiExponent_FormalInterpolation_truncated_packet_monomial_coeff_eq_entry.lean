-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_monomial_coeff_eq_entry
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:13:24.291689+00:00
-- url     : https://prove2.me/submissions/44e56af2-8246-4fec-a2f1-0fa496b830fc

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion_monomial
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open OAI.PiExponent.InterpolationMatrix

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (rho : InterpolationMatrix.Row K v0 theta w H)
    (c : InterpolationMatrix.Column w0 w H) (z : Complex) :
    (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) z)).coeff
        (InterpolationMatrix.exponentVector rho.2.val) =
      z * InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
        (c.1 0) (fun i => c.1 i.succ) := by
  classical
  have hsmul :
      truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) z) =
        z • truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (1 : Complex)) := by
    simp only [truncatedPolynomialJet]
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    simp [Algebra.smul_def]
  rw [hsmul, MvPolynomial.coeff_smul]
  have h1 :=
    truncated_polynomial_jet_support_expansion_monomial
      (j := rho.1.val) (r := r) (T := T) (e := c.1) (a := rho.2.val)
  rw [h1]
  rfl
