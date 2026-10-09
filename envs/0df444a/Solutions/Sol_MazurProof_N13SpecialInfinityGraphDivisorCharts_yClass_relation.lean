-- Prove2me | solution 1 for MazurProof.N13SpecialInfinityGraphDivisorCharts.yClass_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:35:51.027082+00:00
-- url     : https://prove2.me/submissions/247ea55e-1ca8-4787-9d26-092f1e490a4e

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityGraphDivisorCharts =====
section
/-!
# Chart ideals of special infinity-graph divisors

This file identifies the canonical two-chart ideals of the degree-two
divisor obtained from a monic graph on the special infinity chart.  The
key local calculation treats a repeated root directly: the square of the
point ideal equals the quadratic graph ideal because the curve coefficient
`h∞(a)` is a unit at every `F₂`-rational root.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The defining equation of the special infinity chart holds in its
coordinate ring. -/
theorem yClass_relation :
    yClass ^ 2 +
        xClassHom N13SpecialInfinityChart.hPoly * yClass =
      xClassHom N13SpecialInfinityChart.rhsPoly := by
  change
    N13SpecialInfinityChart.vClass ^ 2 +
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.rhsPoly
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13SpecialInfinityChart.curvePoly]
  ring
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end

end

theorem solution : type_of% @MazurProof.N13SpecialInfinityGraphDivisorCharts.yClass_relation := @MazurProof.N13SpecialInfinityGraphDivisorCharts.yClass_relation
