-- Prove2me | solution 1 for MazurProof.N13FormalInfinityBranches.infinityCurvePoly_derivative_mod_x_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:28:36.874164+00:00
-- url     : https://prove2.me/submissions/368ead2d-1dbf-4c92-a05e-e58908693c81

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityBranches =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityBranches =====
section
/-!
# The two Hensel branches at infinity for N13

The formal-infinity equation

`v² + (1 + X² + X³)v - (X + X²) = 0`

reduces modulo `X` to `v(v + 1)`.  Both roots of the special fibre are
simple.  This file lifts the root `0` by X-adic Hensel, obtains the conjugate
root from the quadratic equation, and proves that their difference is a
unit.  These are the structural inputs for splitting the complete
infinity-chart algebra by two-point evaluation.
-/
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13FormalInfinityBranches.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13FormalInfinityBranches.instIsAdicCompletePowerXIdeal
theorem infinityCurvePoly_derivative_eval_zero :
    N13FormalInfinityChart.infinityCurvePoly.derivative.eval 0 =
      N13FormalInfinityChart.hPower := by
  simp [N13FormalInfinityChart.infinityCurvePoly]
theorem infinityCurvePoly_derivative_mod_x_isUnit :
    IsUnit
      (Ideal.Quotient.mk xIdeal
        (N13FormalInfinityChart.infinityCurvePoly.derivative.eval 0)) := by
  rw [infinityCurvePoly_derivative_eval_zero]
  have hmod :
      Ideal.Quotient.mk xIdeal N13FormalInfinityChart.hPower = 1 := by
    have hx : PowerSeries.X ∈ xIdeal :=
      Ideal.subset_span (Set.mem_singleton PowerSeries.X)
    have hx0 :
        Ideal.Quotient.mk xIdeal PowerSeries.X = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simp [N13FormalInfinityChart.hPower, hx0]
  rw [hmod]
  exact isUnit_one
end
end MazurProof.N13FormalInfinityBranches
end

end

theorem solution : type_of% @MazurProof.N13FormalInfinityBranches.infinityCurvePoly_derivative_mod_x_isUnit := @MazurProof.N13FormalInfinityBranches.infinityCurvePoly_derivative_mod_x_isUnit
