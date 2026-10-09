-- Prove2me | solution 1 for MazurProof.N13IntegralInfinityPointSpread.pointResidual_eval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:58:44.010989+00:00
-- url     : https://prove2.me/submissions/9fb71a60-4968-423c-90c2-dd8fbe5a8a29

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
/-!
# Integral point ideals on the N13 infinity chart

An integral point `(t₀,v₀)` on the ordinary infinity chart with
`t₀ ≡ 0 mod 2` defines the linear graph ideal

`(t-t₀, v-v₀)`.

Its generalized Jacobian in the ordinate direction reduces to `1`, hence
is a two-adic unit.  The abstract graph-ideal product theorem then gives an
explicit inverse for this point ideal.  This is the infinity-chart analogue
of the integral affine semigraph construction.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityPointSpread.instFactPrimeOfNatNat_fLT
theorem pointResidual_eval (P : IntegralInfinityPoint) :
    (pointResidual P).eval P.1.1 = 0 := by
  simpa [pointResidual, pointV,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    N13GoodModelTwo.InfinityChartEquation,
    sub_eq_zero] using P.2
/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/
end
end MazurProof.N13IntegralInfinityPointSpread
end

end

theorem solution : type_of% @MazurProof.N13IntegralInfinityPointSpread.pointResidual_eval := @MazurProof.N13IntegralInfinityPointSpread.pointResidual_eval
