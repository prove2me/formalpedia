-- Prove2me | solution 1 for MazurProof.N13SpecialCurveOverlap.affineOverlap_coordinate_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:23:15.847679+00:00
-- url     : https://prove2.me/submissions/bdc81999-409d-4f29-8bdf-59c1811dc9e1

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation

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
/-! ## The reverse chart map -/
/-- The ordinary affine-chart equation in its two named coordinates. -/
theorem affine_coordinate_relation :
    yClass ^ 2 + (xClass ^ 3 + xClass + 1) * yClass =
      xClass ^ 5 + xClass ^ 4 := by
  let φ : R₂[X] →+* AffineCurve :=
    AdjoinRoot.of
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  let root : AffineCurve :=
    AdjoinRoot.root
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  have h :=
    AdjoinRoot.eval₂_root
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
  change
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
      φ root = 0 at h
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    xClass, yClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.yClass,
    N13GeneralizedMumfordIntegral.mk, φ, root] using h
end
end MazurProof.N13OrdinaryCurveOverlap
end

end

-- ===== FLT.Assumptions.MazurProof.N13SpecialCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCurveOverlap =====
section
/-!
# The special algebraic overlap of the two N13 charts

This file begins the special, pre-completion two-chart model.  It localizes
the infinity chart at `t` and constructs the affine restriction by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

The construction uses the universal properties of `AdjoinRoot` and
`Localization.Away`; its equation check is the presentation-independent
identity in `N13OrdinaryOverlapCore`.
-/
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-! ## The reverse chart map -/
/-- The special affine-chart equation in its two named coordinates. -/
theorem affine_coordinate_relation :
    yClass ^ 2 + (xClass ^ 3 + xClass + 1) * yClass =
      xClass ^ 5 + xClass ^ 4 := by
  let φ : K[X] →+* AffineCurve :=
    AdjoinRoot.of
      (N13GoodCoordinateRingTwo.curvePoly)
  let root : AffineCurve :=
    AdjoinRoot.root
      (N13GoodCoordinateRingTwo.curvePoly)
  have h :=
    AdjoinRoot.eval₂_root
      (N13GoodCoordinateRingTwo.curvePoly)
  change
    (N13GoodCoordinateRingTwo.curvePoly).eval₂
      φ root = 0 at h
  simp only [N13GoodCoordinateRingTwo.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul] at h
  apply sub_eq_zero.mp
  simpa [N13GoodCoordinateRingTwo.hPoly,
    N13GoodCoordinateRingTwo.rhsPoly,
    xClass, yClass,
    N13GoodCoordinateRingTwo.xClass,
    N13GoodCoordinateRingTwo.yClass,
    N13GoodCoordinateRingTwo.mk, φ, root] using h
theorem affineOverlap_coordinate_relation :
    yAffineOverlap ^ 2 +
        (xAffineOverlap ^ 3 + xAffineOverlap + 1) *
          yAffineOverlap =
      xAffineOverlap ^ 5 + xAffineOverlap ^ 4 := by
  simpa [xAffineOverlap, yAffineOverlap] using
    congrArg (algebraMap AffineCurve AffineOverlap)
      affine_coordinate_relation
end
end MazurProof.N13SpecialCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13SpecialCurveOverlap.affineOverlap_coordinate_relation := @MazurProof.N13SpecialCurveOverlap.affineOverlap_coordinate_relation
