-- Prove2me | solution 1 for MazurProof.N13SpecialDivisorCharts.map_infinityPointIdeal
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:27:28.268416+00:00
-- url     : https://prove2.me/submissions/1e2effe4-ec2f-49c5-af33-ddb5b2c62d32

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

-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
/-!
# Canonical special-chart ideals of degree-two divisors

The completed special N13 curve is covered by its ordinary affine chart and
its infinity chart.  A finite point with horizontal coordinate zero is absent
from the overlap, a finite point with horizontal coordinate one lies on both
charts, and an infinity point is absent from the ordinary affine chart.

This file assigns to every completed point its compatible pair of chart
ideals.  Products of two point pairs then descend through the symmetric square
to give canonical chart ideals for every effective divisor of degree two.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- Extension of an infinity-chart point ideal to the overlap has the
expected coordinate generators. -/
theorem map_infinityPointIdeal (t v : K) :
    Ideal.map
        (algebraMap SpecialInfinity SpecialOverlap)
        (infinityPointIdeal t v) =
      Ideal.span
        {N13SpecialCurveOverlap.tOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap t,
          N13SpecialCurveOverlap.vOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap v} := by
  simp [infinityPointIdeal, Ideal.map_span, Set.image_pair,
    N13SpecialCurveOverlap.tOverlap,
    N13SpecialCurveOverlap.vOverlap,
    N13SpecialCurveOverlap.coefficientToInfinityOverlap]
end
end MazurProof.N13SpecialDivisorCharts
end

end

theorem solution : type_of% @MazurProof.N13SpecialDivisorCharts.map_infinityPointIdeal := @MazurProof.N13SpecialDivisorCharts.map_infinityPointIdeal
