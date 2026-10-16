-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_log_matrix_mulVecLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:00:44.308201+00:00
-- url     : https://prove2.me/submissions/625bfa57-bb8f-4c0e-b1ed-3d44c3897062

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (c.1 0) (fun i => c.1 i.succ) *
        P.coeff (InterpolationMatrix.exponentVector c.1) := by
  classical
  simp [Matrix.mulVec_eq_sum, InterpolationMatrix.truncatedLogMatrix,
    InterpolationMatrix.matrix, mul_comm]