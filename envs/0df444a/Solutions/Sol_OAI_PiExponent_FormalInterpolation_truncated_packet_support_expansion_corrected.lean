-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:55:23.313428+00:00
-- url     : https://prove2.me/submissions/c24fc0b9-f5cb-4cf4-a033-800850400b25

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_polynomial_jet_support_expansion

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    truncatedPolynomialPacket K v0 theta w H r T P rho =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) := by
  simpa [truncatedPolynomialPacket] using
    OAI.PiExponent.FormalInterpolation.truncated_polynomial_jet_support_expansion
      (j := rho.1.val) r T P rho.2.1