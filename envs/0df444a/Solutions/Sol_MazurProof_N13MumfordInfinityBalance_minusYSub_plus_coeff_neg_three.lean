-- Prove2me | solution 1 for MazurProof.N13MumfordInfinityBalance.minusYSub_plus_coeff_neg_three
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:06:43.953478+00:00
-- url     : https://prove2.me/submissions/5d4ced7b-0a8c-43b2-a6be-f37d956b733f

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13MumfordInfinityBalance_evalSqrtInfinity_coeff_neg_three

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
end
end MazurProof.N13BranchNorm
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordInfinityBalance =====
section
/-!
# Structural infinity balancing for the true `X₁(13)` sextic

The polynomial used here is exactly

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Its positive-infinity cubic part is

`s = X³ + 2X² + X - 1`,

with the exact low-degree identity `f - s² = 4X(X+1)`.  This file builds
the two adapted Cantor lifts needed to balance the integer at infinity.
There is no divisor enumeration or Riemann--Roch input.
-/
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13MumfordInfinityBalance
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
variable (D : N13Mumford.SemiMumford K)
/-! ## The two adapted lifts -/
/-! ## Degree bounds -/
/-! ## Leading terms at the two infinities -/
theorem evalNegMinusLift_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13BranchNorm.evalPoly K (-minusLift D)).coeff (-3 : ℤ) = 1 := by
  rw [show -minusLift D =
      sqrtInfinity + minusRemainder D by
        unfold minusLift
        ring,
    map_add, HahnSeries.coeff_add,
    evalSqrtInfinity_coeff_neg_three]
  rw [evalPoly_coeff_neg_three_eq_zero
    (minusRemainder D) (by
      exact (minusRemainder_natDegree_le_one D hdeg).trans (by omega))]
  norm_num
theorem minusYSub_plus_coeff_neg_three
    (hdeg : D.u.natDegree ≤ 2) :
    (N13Infinity.coordinateToLaurent K
      (ySubClass (N13Mumford.model K) (minusLift D))).coeff
        (-3 : ℤ) = 2 := by
  rw [ySubClass, map_sub,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13Infinity.coordinateToLaurent_xClass]
  change
    (N13Infinity.ySeries K -
      N13BranchNorm.evalPoly K (minusLift D)).coeff (-3 : ℤ) = 2
  have hneg :
      N13BranchNorm.evalPoly K (minusLift D) =
        -N13BranchNorm.evalPoly K (-minusLift D) := by
    simp
  rw [hneg, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    ySeries_coeff_neg_three,
    evalNegMinusLift_coeff_neg_three D hdeg]
  norm_num
/-! ## Exact orders of the principal Cantor corrections -/
/-! ## The two class-preserving balancing steps -/
/-! ## A well-founded measure for the two balance walls -/
/-! ## Structural infinity balancing -/
end
end MazurProof.N13MumfordInfinityBalance
end

end

theorem solution : type_of% @MazurProof.N13MumfordInfinityBalance.minusYSub_plus_coeff_neg_three := @MazurProof.N13MumfordInfinityBalance.minusYSub_plus_coeff_neg_three
