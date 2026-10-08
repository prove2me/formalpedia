-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:33:55.234986+00:00
-- url     : https://prove2.me/submissions/3ddddee5-0ac0-457a-b446-718d52b65268
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)) :
    ∀ ρ : Row d (H : ℝ),
      (actualMatrix d (H : ℝ)).mulVecLin
        (fun c : Column d (H : ℝ) => P.val.coeff (InterpolationMatrix.exponentVector c.1)) ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by
  intro ρ
  have hw : ∀ i : Fin d.m, 0 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    dsimp [MatrixArithmetic.logWeights]
    positivity
  have h := OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff
    d.w0 d.v0 d.base.theta H (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    P d.v0_pos d.base.theta_pos hw hT ρ
  simpa [DeterminantContradiction.actualMatrix, MatrixArithmetic.truncationOrders,
    MatrixArithmetic.rationalCenters, DeterminantContradiction.finiteNumerators,
    DeterminantContradiction.finiteDenominators, FormalInterpolation.packetMap] using h
