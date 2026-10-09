-- Prove2me | solution 1 for MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:51:26.238986+00:00
-- url     : https://prove2.me/submissions/3818646b-1339-4668-a2d3-f2b4f511f160

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
theorem good_root_relation :
    N13GeneralizedMumfordIntegral.yClass ^ 2 +
        goodXHom (K := K) (hPoly (K := K)) *
          N13GeneralizedMumfordIntegral.yClass -
      goodXHom (K := K) (rhsPoly (K := K)) = 0 := by
  apply sub_eq_zero.mpr
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13GeneralizedMumfordIntegral.curvePoly]
  ring
theorem sexticYInGood_root :
    (SexticMumford.curvePoly (M (K := K))).eval₂
      (goodXHom (K := K)) (sexticYInGood (K := K)) = 0 := by
  simp only [SexticMumford.curvePoly,
    eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change
    sexticYInGood (K := K) ^ 2 -
      goodXHom (K := K) (N13Mumford.f K) = 0
  rw [sextic_eq_h_sq_add_four_rhs (K := K)]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  unfold sexticYInGood
  linear_combination 4 * good_root_relation (K := K)
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

theorem solution : type_of% @MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root := @MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root
