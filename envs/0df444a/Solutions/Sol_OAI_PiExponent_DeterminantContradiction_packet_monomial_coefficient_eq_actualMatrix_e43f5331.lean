-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_monomial_coefficient_eq_actualMatrix_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:15:28.903676+00:00
-- url     : https://prove2.me/submissions/3dd97a99-35cb-455a-b710-e65a2e5fcf67

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_bridge

open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (rho : Row d H) (c : Column d H) (z : Complex) :
    (truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.C z *
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1)).coeff
      (InterpolationMatrix.exponentVector rho.2.1) =
    z * actualMatrix d H rho c := by
  have hcol : Fin.cases (c.1 0) (fun i => c.1 i.succ) = c.1 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hrow : Fin.cases (rho.2.1 0) (fun i => rho.2.1 i.succ) = rho.2.1 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [← hcol, ← hrow]
  simpa [DeterminantContradiction.actualMatrix,
    InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix,
    InterpolationMatrix.entry, MatrixArithmetic.rationalCenters,
    MatrixArithmetic.truncationOrders, DeterminantContradiction.finiteNumerators,
    DeterminantContradiction.finiteDenominators] using
      (OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_bridge
        d.m
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        rho.1.val (c.1 0) (fun i => c.1 i.succ)
        (fun i => rho.2.1 i.succ) (rho.2.1 0) z)