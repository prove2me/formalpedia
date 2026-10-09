-- Prove2me | solution 1 for MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:10.202991+00:00
-- url     : https://prove2.me/submissions/776f75e3-b40d-4ec8-b44a-e00dfd4c5472

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
namespace Model
end Model
variable (M : Model K)
/-! ## The affine coordinate ring -/
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
/-! ## Balanced triples -/
/-! ## Curve points and their balanced representatives -/
/-! ## Mumford ideals -/
/-! ## The oriented fractional-ideal quotient -/
end
end MazurProof.SexticMumford
end

end

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
theorem goodYInSextic_root :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (sexticXHom (K := K)) (goodYInSextic (K := K)) = 0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  have hy := SexticMumford.yClass_sq (M (K := K))
  change
    SexticMumford.yClass (M (K := K)) ^ 2 =
      sexticXHom (K := K) (N13Mumford.f K) at hy
  rw [sextic_eq_h_sq_add_four_rhs (K := K)] at hy
  simp only [map_add, map_mul, map_pow, map_ofNat] at hy
  let a : SexticRing (K := K) :=
    (algebraMap K (SexticRing (K := K))) (1 / 2)
  let Y : SexticRing (K := K) :=
    SexticMumford.yClass (M (K := K))
  let H : SexticRing (K := K) :=
    sexticXHom (K := K) (hPoly (K := K))
  let R : SexticRing (K := K) :=
    sexticXHom (K := K) (rhsPoly (K := K))
  simp only [goodYInSextic, Algebra.smul_def]
  change (a * (Y - H)) ^ 2 + H * (a * (Y - H)) - R = 0
  have hy' : Y ^ 2 = H ^ 2 + 4 * R := hy
  have ha : 2 * a = 1 := by
    dsimp only [a]
    rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
      ← map_mul]
    norm_num
  linear_combination
    a ^ 2 * hy' +
      (-a * Y * H + a * H ^ 2 + (2 * a + 1) * R) * ha
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

theorem solution : type_of% @MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root := @MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root
