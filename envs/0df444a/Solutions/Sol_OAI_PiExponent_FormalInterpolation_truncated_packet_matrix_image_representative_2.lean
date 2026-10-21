-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_image_representative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:38:16.988565+00:00
-- url     : https://prove2.me/submissions/79343c4b-32c4-4f44-a3d2-9387f1402580

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_is_column_monomial_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_column_monomial_sum

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      truncatedPolynomialPacket K v0 theta w H r T Q.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
      w0 w H x
  refine ⟨Q, ?_⟩
  rw [hQ]
  exact OAI.PiExponent.FormalInterpolation.truncated_packet_column_monomial_sum
    K w0 v0 theta w H r T x