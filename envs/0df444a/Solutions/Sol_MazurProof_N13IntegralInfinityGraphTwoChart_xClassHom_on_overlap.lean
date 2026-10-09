-- Prove2me | solution 1 for MazurProof.N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:54:23.082667+00:00
-- url     : https://prove2.me/submissions/e313dc29-882f-4a04-bdb1-1db9897ac2fc

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityGraphTwoChart =====
section
/-!
# Two-chart closures of integral N13 infinity graphs

An integral polynomial graph on the ordinary infinity chart can be
homogenized with the weights

`u ↦ X² u(X⁻¹)`, `v ↦ X³ v(X⁻¹)`, `w ↦ X⁴ w(X⁻¹)`.

`Polynomial.reflect` implements these three weighted reversals.  Reflecting
the infinity semigraph identity at total weight six gives the affine
semigraph identity, while on the Laurent overlap the two graph generators
differ by the units `x²` and `x³`.  Thus every bounded integral infinity
graph supplies an invertible root-free two-chart line.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphTwoChart.instFactPrimeOfNatNat_fLT
/-- The infinity horizontal coordinate map evaluates polynomials at the
Laurent-overlap coordinate `t`. -/
theorem xClassHom_on_overlap
    (p : Base) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      p.eval₂
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
        N13OrdinaryCurveOverlap.tOverlap := by
  let f : Base →+* N13OrdinaryCurveOverlap.InfinityOverlap :=
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap).comp
        N13IntegralInfinityGraphJacobian.xClassHom
  let g : Base →+* N13OrdinaryCurveOverlap.InfinityOverlap :=
    Polynomial.eval₂RingHom
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.tOverlap
  have hfg : f = g := by
    ext r <;>
      simp [f, g,
        N13IntegralInfinityGraphJacobian.xClassHom,
        N13IntegralInfinityPointSpread.xClassHom,
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap,
        N13OrdinaryCurveOverlap.tOverlap,
        N13IntegralInfinityChart.tClass]
  exact congrArg (fun φ : Base →+* _ => φ p) hfg
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end

end

theorem solution : type_of% @MazurProof.N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap := @MazurProof.N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap
