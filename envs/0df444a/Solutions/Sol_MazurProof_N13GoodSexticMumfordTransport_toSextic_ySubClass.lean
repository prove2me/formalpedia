-- Prove2me | solution 1 for MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:45:14.311457+00:00
-- url     : https://prove2.me/submissions/384de694-b87e-4444-b0d5-050de60e7746

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_goodYInSextic_root

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

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
@[simp] theorem toSextic_yClass :
    toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  AdjoinRoot.lift_root (goodYInSextic_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/
open Polynomial
namespace MazurProof.N13GoodSexticMumfordTransport
noncomputable section
open N13GoodSexticCoordinateEquiv
universe u
variable {K : Type u} [Field K] [CharZero K]
theorem two_mul_invTwo :
    (2 : (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) *
        (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) 2, ← map_mul]
  norm_num
/-- Under completion of the square, the generalized graph generator is
`1 / 2` times the corresponding sextic graph generator. -/
@[simp] theorem toSextic_ySubClass (v : K[X]) :
    (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.ySubClass v) =
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ *
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) (completedGraph v) := by
  simp only [N13GeneralizedMumfordIntegral.ySubClass, map_sub,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    N13GoodSexticCoordinateEquiv.goodYInSextic,
    SexticMumford.ySubClass, completedGraph, Algebra.smul_def]
  have hhalf :
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (1 / 2 : K) =
        (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ := by
    norm_num
  have hx :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
          (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
        2 * SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v +
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
            N13GeneralizedMumfordIntegral.hPoly := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K))
        (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
      2 * (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v +
        (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) N13GeneralizedMumfordIntegral.hPoly
    rw [map_add, map_mul, map_ofNat]
  rw [hhalf, hx]
  let a : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹
  let Y : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) := SexticMumford.yClass (N13GoodSexticCoordinateEquiv.M (K := K))
  let H : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
      N13GeneralizedMumfordIntegral.hPoly
  let V : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v
  change a * (Y - H) - V = a * (Y - (2 * V + H))
  have ha : 2 * a = 1 := two_mul_invTwo
  linear_combination V * ha
end
end MazurProof.N13GoodSexticMumfordTransport
end

end

theorem solution : type_of% @MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass := @MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
