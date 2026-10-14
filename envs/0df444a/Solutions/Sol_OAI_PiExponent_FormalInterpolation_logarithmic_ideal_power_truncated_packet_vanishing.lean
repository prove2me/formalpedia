-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_ideal_power_truncated_packet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:46:35.812643+00:00
-- url     : https://prove2.me/submissions/c8d80e10-fac7-4181-a49e-f5053b85f97c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_packets_vanish
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishing_on_ideal_implies_vanishing_on_powers

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (hscale : ∀ i, R ≤ (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ (logarithmicCentersIdeal
      (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by
  exact OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_implies_vanishing_on_powers
    K v0 theta w r R T hR hw
    (logarithmicCentersIdeal (fun j : Fin K => fun i => (j.val : Complex) * r i) T e)
    (by
      intro Q hQ
      exact OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_packets_vanish
        K v0 theta w r R T e hv0 htheta hw hR hscale Q hQ)
    n P hP