-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.bounded_truncated_packet_matrix_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:42:08.281332+00:00
-- url     : https://prove2.me/submissions/1ad97530-56f3-4d6b-8e71-e13356108087
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    ∃ x : InterpolationMatrix.Column w0 w H → Complex,
      truncatedPolynomialPacket K v0 theta w H r T P.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by
  refine ⟨fun c => P.val.coeff (InterpolationMatrix.exponentVector c.1), ?_⟩
  exact OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights
    K w0 v0 theta w H r T hw0 hw P