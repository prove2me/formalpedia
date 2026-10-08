-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedJetPacket_surjective_of_fullPacket
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T07:01:27.29728+00:00
-- url     : https://prove2.me/submissions/295a8af2-0c81-4093-85ea-c513d31dee9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_truncatedJetCoeff
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (H : Rat)
    (hT : forall i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : Real) <=
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : Real) *
          (d.v0 : Real))
    (hpacket : Function.Surjective
      (FormalInterpolation.packetMap d (H : Real))) :
    Function.Surjective
      (fun P : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) (H : Real) =>
        fun rho : Row d H =>
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
            (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
              (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
                  MatrixArithmetic.rationalCenters (finiteNumerators d)
                    (finiteDenominators d) i) + MvPowerSeries.X i.succ +
                FormalInterpolation.liftSeries d.m
                  ((PowerSeries.trunc
                    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                    (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val)) := by
  intro y
  obtain ⟨P, hP⟩ := hpacket y
  refine ⟨P, ?_⟩
  funext rho
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
      (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
        (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
            MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d) i) + MvPowerSeries.X i.succ +
          FormalInterpolation.liftSeries d.m
            ((PowerSeries.trunc
              (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
              (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val) = y rho
  rw [← FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff d H P rho]
  rw [FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff_explicit_coefficients
    d (H : Real) P hT rho]
  exact congrFun hP rho
