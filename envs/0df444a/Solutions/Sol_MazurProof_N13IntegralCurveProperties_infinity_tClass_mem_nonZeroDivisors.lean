-- Prove2me | solution 1 for MazurProof.N13IntegralCurveProperties.infinity_tClass_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:02:21.033987+00:00
-- url     : https://prove2.me/submissions/fad34847-4390-41b7-8d1f-5cdc3ec64ba6

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

-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveProperties =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralCurveProperties =====
section
/-!
# Integrality of the ordinary N13 model

The affine chart embeds in its rational generic fibre.  On the infinity
chart, the parameter `t` is regular because the coordinate ring is free over
`ℤ₂[t]`; localizing at `t` identifies it with the affine overlap.  Thus both
charts and their common principal open are domains.

The two irreducible chart images cover the glued scheme and have nonempty
intersection.  This proves that the ordinary two-chart N13 model is reduced,
irreducible, and integral without any point enumeration.
-/
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
attribute [local instance] MazurProof.N13IntegralCurveProperties.instFactPrimeOfNatNat_fLT
open AlgebraicGeometry
/-- The infinity parameter is a non-zero-divisor.  This is the free-module
argument: multiplication by `t` is scalar multiplication by the nonzero
polynomial `X` on a free `ℤ₂[t]`-module. -/
theorem infinity_tClass_mem_nonZeroDivisors :
    N13IntegralInfinityChart.tClass ∈
      nonZeroDivisors InfinityCurve := by
  apply IsRegular.mem_nonZeroDivisors
  rw [← isLeftRegular_iff_isRegular]
  intro z w h
  apply
    (IsRegular.of_ne_zero
      (Polynomial.X_ne_zero :
        (Polynomial.X :
          N13IntegralInfinityChart.Base) ≠ 0)).smul_right_injective
      InfinityCurve
  simpa [N13IntegralInfinityChart.tClass,
    Algebra.smul_def] using h
end
end MazurProof.N13IntegralCurveProperties
end

end

theorem solution : type_of% @MazurProof.N13IntegralCurveProperties.infinity_tClass_mem_nonZeroDivisors := @MazurProof.N13IntegralCurveProperties.infinity_tClass_mem_nonZeroDivisors
