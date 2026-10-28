-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_column_sum_linear
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:01:21.985372+00:00
-- url     : https://prove2.me/submissions/34339111-841a-4162-af09-154a8c6d07de


import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    truncatedPolynomialPacket K v0 theta w H r T
        (∑ c : InterpolationMatrix.Column w0 w H,
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) rho =
      ∑ c : InterpolationMatrix.Column w0 w H,
        truncatedPolynomialPacket K v0 theta w H r T
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) rho := by
  classical
  simp only [truncatedPolynomialPacket]
  let φ := truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T
  have hφ : φ (∑ c : InterpolationMatrix.Column w0 w H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        φ (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) := by
    exact map_sum (φ : MvPolynomial (Fin (m + 1)) Complex →+* MvPolynomial (Fin (m + 1)) Complex)
      _ _
  rw [hφ, MvPolynomial.coeff_sum]
