-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.matrix_surjective_of_packets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:36:13.088114+00:00
-- url     : https://prove2.me/submissions/aff010c6-1343-4caf-b42c-62ed9c3eadf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_truncatedJetCoeff
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJetPacket_surjective_of_fullPacket

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (H : Rat)
    (hT : forall i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : Real) <=
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : Real) *
          (d.v0 : Real))
    (hpacket : Function.Surjective (FormalInterpolation.packetMap d (H : Real))) :
    Function.Surjective (actualMatrix d (H : Real)).mulVecLin := by
  have htruncated :=
    FormalInterpolation.truncatedJetPacket_surjective_of_fullPacket d H hT hpacket
  intro y
  obtain ⟨P, hP⟩ := htruncated y
  refine ⟨fun c : Column d (H : Real) =>
    P.val.coeff (InterpolationMatrix.exponentVector c.1), ?_⟩
  funext rho
  rw [FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff]
  exact congrFun hP rho
