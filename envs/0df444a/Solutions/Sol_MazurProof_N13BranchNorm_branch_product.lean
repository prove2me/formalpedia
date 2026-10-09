-- Prove2me | solution 1 for MazurProof.N13BranchNorm.branch_product
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:14:21.377607+00:00
-- url     : https://prove2.me/submissions/05e9db01-5ecb-4398-b80a-1ab6658b3bec

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13Infinity_ySeries_sq

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)
@[simp] theorem coordinateToLaurent_linearFunction (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) =
      evalPoly K p + evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, coordinateToLaurent_yClass]
@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring
theorem branch_product (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) *
        N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) =
      evalPoly K (normNumerator K p q) := by
  rw [coordinateToLaurent_linearFunction,
    coordinateToLaurentMinus_linearFunction]
  calc
    (evalPoly K p + evalPoly K q * N13Infinity.ySeries K) *
          (evalPoly K p - evalPoly K q * N13Infinity.ySeries K) =
        evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * N13Infinity.ySeries K ^ 2 := by ring
    _ = evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * evalPoly K (N13Mumford.f K) := by
            have hy :
                N13Infinity.ySeries K ^ 2 =
                  evalPoly K (N13Mumford.f K) := by
              simpa only [evalPoly_apply] using
                N13Infinity.ySeries_sq K
            rw [hy]
    _ = evalPoly K (normNumerator K p q) := by
      simp only [normNumerator, map_sub, map_mul, map_pow]
end
end MazurProof.N13BranchNorm
end

end

theorem solution : type_of% @MazurProof.N13BranchNorm.branch_product := @MazurProof.N13BranchNorm.branch_product
