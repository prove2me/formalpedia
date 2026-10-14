-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_image_representative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:35:04.285007+00:00
-- url     : https://prove2.me/submissions/cb772b12-b2c3-40db-b4a6-c92e3a2acdd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_realizes_column_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      truncatedPolynomialPacket K v0 theta w H r T Q.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by
  obtain ⟨Q, hcoeff⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_polynomial_realizes_column_coefficients
      w0 w H x
  refine ⟨Q, ?_⟩
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients]
  congr 1
  funext c
  exact hcoeff c
