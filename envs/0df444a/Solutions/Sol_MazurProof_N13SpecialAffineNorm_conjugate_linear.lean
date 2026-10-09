-- Prove2me | solution 1 for MazurProof.N13SpecialAffineNorm.conjugate_linear
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:53:57.542989+00:00
-- url     : https://prove2.me/submissions/c324f16d-6425-4c4f-b80f-30a6b17dcf61

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialAffineNorm =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual hyperelliptic conjugation and polynomial norm on the good
characteristic-two affine coordinate ring. This is not the bad sextic
obtained by dividing the ordinate by two. Nonzero functions have nonzero
norm, and the comparison factor pair makes the norm divide an explicit
polynomial supported only over x=0 and x=1.
-/
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts
@[simp] theorem conjugate_xClass (p : K[X]) : conjugate (xClass p) = xClass p :=
  AdjoinRoot.lift_of _
@[simp] theorem conjugate_yClass : conjugate yClass = -xClass hPoly - yClass :=
  AdjoinRoot.lift_root _
theorem conjugate_linear (p q : K[X]) :
    conjugate (linear p q) = linear (p - q * hPoly) (-q) := by
  simp only [linear, map_add, map_mul, conjugate_xClass, conjugate_yClass,
    xClass_sub, xClass_mul, xClass_neg]
  ring
open N13SpecialComparisonFactorPair hiding xClass R
end
end MazurProof.N13SpecialAffineNorm
end

end

theorem solution : type_of% @MazurProof.N13SpecialAffineNorm.conjugate_linear := @MazurProof.N13SpecialAffineNorm.conjugate_linear
