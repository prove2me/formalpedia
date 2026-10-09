-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:32:44.631989+00:00
-- url     : https://prove2.me/submissions/c3a65396-6099-48a3-a775-869bf771eb82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedLogMatrix_mulVec_eq_truncatedJetCoeff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (H : Rat)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) (H : Real)) :
    forall rho : Row d H,
      (actualMatrix d (H : Real)).mulVecLin
          (fun c : Column d (H : Real) =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
                MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d) i) + MvPowerSeries.X i.succ +
              FormalInterpolation.liftSeries d.m
                ((PowerSeries.trunc
                  (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                  (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val) := by
  simpa [actualMatrix] using
    OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_truncatedJetCoeff
      d.K d.w0 d.v0 d.base.theta (H : Real)
      (MatrixArithmetic.logWeights (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      P
