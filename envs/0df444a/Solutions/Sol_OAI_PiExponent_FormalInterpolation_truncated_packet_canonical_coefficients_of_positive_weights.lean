-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:47:23.733987+00:00
-- url     : https://prove2.me/submissions/147474d9-01ab-43ed-b11b-aba884c1fbfe

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by
  apply OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
  exact OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
    w0 w H hw0 hw P
