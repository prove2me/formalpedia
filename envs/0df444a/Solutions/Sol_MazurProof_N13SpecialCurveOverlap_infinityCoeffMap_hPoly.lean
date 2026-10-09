-- Prove2me | solution 1 for MazurProof.N13SpecialCurveOverlap.infinityCoeffMap_hPoly
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:25:49.690608+00:00
-- url     : https://prove2.me/submissions/80e80d14-ec43-4a6e-a55a-b8808c9d9299

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
@[simp] theorem infinityCoeffMap_hPoly :
    infinityCoeffMap N13SpecialInfinityChart.hPoly =
      1 + tAffineOverlap ^ 2 + tAffineOverlap ^ 3 := by
  simp [infinityCoeffMap, coefficientToAffineOverlap,
    N13SpecialInfinityChart.hPoly]
end
end MazurProof.N13SpecialCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13SpecialCurveOverlap.infinityCoeffMap_hPoly := @MazurProof.N13SpecialCurveOverlap.infinityCoeffMap_hPoly
