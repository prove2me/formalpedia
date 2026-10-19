-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_invariant_under_ideal_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:09:50.269393+00:00
-- url     : https://prove2.me/submissions/16d942ac-ac46-4f58-8c5e-b4b22936a97e

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_difference_coeff_vanishes

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i) :
    ∀ n : Nat,
      ∀ P Q : MvPolynomial (Fin (m + 1)) Complex,
        P - Q ∈
          (logarithmicCentersIdeal
            (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n →
        truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P =
          truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T Q := by
  intro n P Q hPQ
  funext rho
  have hz :=
    OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_difference_coeff_vanishes
      K v0 theta w R e T r hR he hscale n P Q hPQ rho
  apply sub_eq_zero.mp
  simpa [truncatedPolynomialPacket, map_sub] using hz