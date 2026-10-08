-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.matrix_surjective_of_packets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:49:57.605995+00:00
-- url     : https://prove2.me/submissions/970c1c98-e835-43f7-ba02-d5eec7176d25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ))
    (hpacket : Function.Surjective (FormalInterpolation.packetMap d (H : ℝ))) :
    Function.Surjective (actualMatrix d (H : ℝ)).mulVecLin := by
  intro y
  obtain ⟨P, hP⟩ := hpacket y
  obtain ⟨x, hx⟩ :=
    FormalInterpolation.actualMatrix_mulVec_eq_packetMap d H P
  refine ⟨x, ?_⟩
  funext ρ
  exact (hx ρ).trans (congrFun hP ρ)
