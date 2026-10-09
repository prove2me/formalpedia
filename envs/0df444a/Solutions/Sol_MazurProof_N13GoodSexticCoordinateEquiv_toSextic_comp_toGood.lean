-- Prove2me | solution 1 for MazurProof.N13GoodSexticCoordinateEquiv.toSextic_comp_toGood
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:44:52.25707+00:00
-- url     : https://prove2.me/submissions/91dc7d79-bdde-44d8-a337-5f0294a8ffa9

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_goodYInSextic_root
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_sexticYInGood_root

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
@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (sexticYInGood_root (K := K))
@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (sexticYInGood_root (K := K))
theorem two_mul_invTwo_sextic :
    (2 : SexticRing (K := K)) *
        (algebraMap K (SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
    ← map_mul]
  norm_num
theorem toSextic_comp_toGood :
    (toSextic (K := K)).comp (toGood (K := K)) =
      RingHom.id (SexticRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toSextic (K := K)
          (toGood (K := K) (sexticXHom (K := K) p)) =
        sexticXHom (K := K) p
    rw [sexticXHom_apply, toGood_xClass, toSextic_xClass]
  · change
      toSextic (K := K)
          (toGood (K := K)
            (SexticMumford.yClass (M (K := K)))) =
        SexticMumford.yClass (M (K := K))
    rw [toGood_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [map_ofNat, ← mul_assoc,
      two_mul_invTwo_sextic (K := K)]
    ring
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

theorem solution : type_of% @MazurProof.N13GoodSexticCoordinateEquiv.toSextic_comp_toGood := @MazurProof.N13GoodSexticCoordinateEquiv.toSextic_comp_toGood
