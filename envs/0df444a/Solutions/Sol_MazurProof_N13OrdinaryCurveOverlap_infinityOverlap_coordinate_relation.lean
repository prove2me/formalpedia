-- Prove2me | solution 1 for MazurProof.N13OrdinaryCurveOverlap.infinityOverlap_coordinate_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:14:11.302986+00:00
-- url     : https://prove2.me/submissions/9ad0d312-6b1b-4879-ac92-d66c7d118c43

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap =====
section
/-!
# The ordinary algebraic overlap of the two N13 charts

This file begins the ordinary, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13OrdinaryCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The ordinary infinity-chart equation in its two named coordinates. -/
theorem infinity_coordinate_relation :
    N13IntegralInfinityChart.vClass ^ 2 +
        (1 + N13IntegralInfinityChart.tClass ^ 2 +
            N13IntegralInfinityChart.tClass ^ 3) *
          N13IntegralInfinityChart.vClass =
      N13IntegralInfinityChart.tClass +
        N13IntegralInfinityChart.tClass ^ 2 := by
  let φ : Base →+* InfinityCurve :=
    AdjoinRoot.of N13IntegralInfinityChart.infinityCurvePoly
  let root : InfinityCurve :=
    AdjoinRoot.root N13IntegralInfinityChart.infinityCurvePoly
  have h :=
    AdjoinRoot.eval₂_root
      N13IntegralInfinityChart.infinityCurvePoly
  change
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
      φ root = 0 at h
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    N13IntegralInfinityChart.tClass,
    N13IntegralInfinityChart.vClass, φ, root] using h
theorem infinityOverlap_coordinate_relation :
    vOverlap ^ 2 +
        (1 + tOverlap ^ 2 + tOverlap ^ 3) * vOverlap =
      tOverlap + tOverlap ^ 2 := by
  simpa [tOverlap, vOverlap] using
    congrArg (algebraMap InfinityCurve InfinityOverlap)
      infinity_coordinate_relation
/-! ## The reverse chart map -/
end
end MazurProof.N13OrdinaryCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13OrdinaryCurveOverlap.infinityOverlap_coordinate_relation := @MazurProof.N13OrdinaryCurveOverlap.infinityOverlap_coordinate_relation
