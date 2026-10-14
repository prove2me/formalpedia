-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_implies_vanishing_on_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:01:26.473204+00:00
-- url     : https://prove2.me/submissions/8457caf5-095b-4ee9-81d9-1c7edbe36ab1

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishes_on_products_of_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishing_on_ideal_power_of_products

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hI : ∀ Q : MvPolynomial (Fin (m + 1)) Complex, Q ∈ I →
      truncatedPolynomialPacket K v0 theta w R r T Q = 0)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ I ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by
  apply OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_power_of_products
    K v0 theta w r R T hR hw I n
  · intro f hf
    exact OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_of_ideal
      K v0 theta w r R T hR hw I hI n f hf
  · exact hP
