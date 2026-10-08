-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:14:38.608295+00:00
-- url     : https://prove2.me/submissions/9b6fd6ed-71ea-43e8-8ca4-e2b960290b19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)) :
    ∃ x : Column d (H : ℝ) → ℂ,
      ∀ ρ : Row d (H : ℝ),
        (actualMatrix d (H : ℝ)).mulVecLin x ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by
  refine ⟨fun c => P.val.coeff (InterpolationMatrix.exponentVector c.1), ?_⟩
  exact OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
    d H P hT
