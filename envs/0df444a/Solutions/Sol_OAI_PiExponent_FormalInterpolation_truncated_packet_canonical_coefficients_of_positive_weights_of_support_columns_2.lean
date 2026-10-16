-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:52:12.076158+00:00
-- url     : https://prove2.me/submissions/6f5bcbdb-2961-4a00-8d78-27d4b15504ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_expansion_corrected
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_sum_eq_mulVec_corrected

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ a ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = a) :
    truncatedPolynomialPacket K v0 theta w H r T P =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1)) := by
  funext rho
  exact (truncated_packet_support_expansion_corrected
      K w0 v0 theta w H r T P rho).trans
    (truncated_packet_support_sum_eq_mulVec_corrected
      K w0 v0 theta w H r T P hcols rho)