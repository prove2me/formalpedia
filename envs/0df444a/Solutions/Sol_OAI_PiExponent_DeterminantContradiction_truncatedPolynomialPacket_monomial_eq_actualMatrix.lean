-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_monomial_eq_actualMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:45:04.83118+00:00
-- url     : https://prove2.me/submissions/5469457b-8a9a-4132-834f-5a7c38bc19f6

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real) (rho : Row d H)
    (c : Column d H) :
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1) rho =
    actualMatrix d H rho c := by
  have hrow :
      Fin.cases (rho.2.1 0) (fun i : Fin d.m => rho.2.1 i.succ) = rho.2.1 := by
    funext i
    cases i using Fin.cases <;> rfl
  have hcol :
      Fin.cases (c.1 0) (fun i : Fin d.m => c.1 i.succ) = c.1 := by
    funext i
    cases i using Fin.cases <;> rfl
  simpa [FormalInterpolation.truncatedPolynomialPacket,
    FormalInterpolation.truncatedPolynomialJet,
    DeterminantContradiction.actualMatrix,
    InterpolationMatrix.truncatedLogMatrix,
    InterpolationMatrix.matrix,
    MatrixArithmetic.rationalCenters,
    DeterminantContradiction.finiteNumerators,
    DeterminantContradiction.finiteDenominators, hrow, hcol] using
    OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
      (m := d.m)
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (fun i => InterpolationMatrix.truncatedLog
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i))
      (j := rho.1.val)
      (s := rho.2.1 0)
      (h := c.1 0)
      (b := fun i : Fin d.m => rho.2.1 i.succ)
      (a := fun i : Fin d.m => c.1 i.succ)