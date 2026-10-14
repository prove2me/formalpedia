-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_truncated_polynomial_jets_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:06:04.77864+00:00
-- url     : https://prove2.me/submissions/1a4431a5-9b89-437c-8af3-bc726c0524e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_truncated_log_matrix_surjective_of_distinct_centers
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_realizes_column_coefficients
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hcenters : Function.Injective
      (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i)) :
    Function.Surjective (truncatedPolynomialPacket K v0 theta w H r T) := by
  intro y
  obtain ⟨x, hx⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_truncated_log_matrix_surjective_of_distinct_centers
      K 1 v0 theta w H r T hcenters y
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_polynomial_realizes_column_coefficients
      (w0 := 1) w H x
  refine ⟨Q.val, ?_⟩
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients
    K 1 v0 theta w H r T Q]
  have hcoeff : (fun c : InterpolationMatrix.Column 1 w H =>
      Q.val.coeff (InterpolationMatrix.exponentVector c.1)) = x := by
    funext c
    exact hQ c
  rw [hcoeff]
  exact hx
