-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_mulVec_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:56:12.076113+00:00
-- url     : https://prove2.me/submissions/0e1b4174-aa3e-4210-bdcd-abeea1ea5aa9

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_sum_eq_column_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_matrix_mulVecLin_apply
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) =
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho := by
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_column_sum
    K w0 v0 theta w H r T P hcols rho]
  exact OAI.PiExponent.FormalInterpolation.truncated_log_matrix_mulVecLin_apply
    K w0 v0 theta w H r T P rho
