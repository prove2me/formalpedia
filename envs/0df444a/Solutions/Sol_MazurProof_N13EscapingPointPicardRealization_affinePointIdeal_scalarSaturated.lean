-- Prove2me | solution 1 for MazurProof.N13EscapingPointPicardRealization.affinePointIdeal_scalarSaturated
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:41:31.732373+00:00
-- url     : https://prove2.me/submissions/cc6c1c1d-5f84-4327-b6d9-b6fd326385c5

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_infinityOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Definitions.Def_MazurN13_L4


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13EscapingPointPicardRealization
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13EscapingPointPicardRealization.instFactPrimeOfNatNat_fLT

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem xClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    xClass u ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem ySubClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    ySubClass xClass yClass v ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num
end
end MazurProof.N13IntegralInfinityChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineCoeffMap_C (r : R₂) :
    affineCoeffMap (C r) = coefficientToInfinityOverlap r := by
  simp [affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineCoeffMap_X :
    affineCoeffMap X = xOverlap := by
  simp [affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affineCurve_relation :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
        affineCoeffMap affineYImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
      tOverlap xOverlap vOverlap
      tOverlap_mul_xOverlap infinityOverlap_coordinate_relation
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, affineCoeffMap_hPoly,
    affineCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction of the affine coordinate ring to the ordinary infinity
principal open. -/
def affineToInfinityOverlap :
    AffineCurve →+* InfinityOverlap :=
  AdjoinRoot.lift affineCoeffMap affineYImage affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_of (p : R₂[X]) :
    affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)) p) =
      affineCoeffMap p := by
  exact AdjoinRoot.lift_of affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClassHom (p : R₂[X]) :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) =
      affineCoeffMap p :=
  affineToInfinityOverlap_of p
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk, affineCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_yClass :
    affineToInfinityOverlap yClass = affineYImage := by
  exact AdjoinRoot.lift_root affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_generalized_yClass :
    affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      affineYImage :=
  affineToInfinityOverlap_yClass
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affine_xClass_mapsToUnit :
    IsUnit (affineToInfinityOverlap xClass) := by
  rw [affineToInfinityOverlap_xClass]
  exact xOverlap_isUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The induced restriction from the affine principal open to the infinity
principal open. -/
def affineOverlapToInfinityOverlap :
    AffineOverlap →+* InfinityOverlap :=
  IsLocalization.Away.lift xClass affine_xClass_mapsToUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_algebraMap
    (z : AffineCurve) :
    affineOverlapToInfinityOverlap
        (algebraMap AffineCurve AffineOverlap z) =
      affineToInfinityOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      xClass affine_xClass_mapsToUnit z
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurve_relation :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hBase,
    infinityCoeffMap_rhsBase]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction of the infinity coordinate ring to the ordinary affine
principal open. -/
def infinityToAffineOverlap :
    InfinityCurve →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13IntegralInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13IntegralInfinityChart.tClass, infinityCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13IntegralInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_tClass_mapsToUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : InfinityCurve) :
    infinityOverlapToAffineOverlap
        (algebraMap InfinityCurve InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13IntegralInfinityChart.tClass
      infinity_tClass_mapsToUnit z
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_xAffineOverlap :
    affineOverlapToInfinityOverlap xAffineOverlap = xOverlap := by
  rw [xAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_xClass]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse overlap map sends `t⁻¹` back to `x`. -/
@[simp] theorem infinityOverlapToAffineOverlap_xOverlap :
    infinityOverlapToAffineOverlap xOverlap = xAffineOverlap := by
  have hinv :
      tAffineOverlap *
          infinityOverlapToAffineOverlap xOverlap = 1 := by
    calc
      tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap =
          infinityOverlapToAffineOverlap tOverlap *
            infinityOverlapToAffineOverlap xOverlap := by
              rw [infinityOverlapToAffineOverlap_tOverlap]
      _ =
          infinityOverlapToAffineOverlap
            (tOverlap * xOverlap) := by
              rw [map_mul]
      _ = 1 := by rw [tOverlap_mul_xOverlap, map_one]
  calc
    infinityOverlapToAffineOverlap xOverlap =
        1 * infinityOverlapToAffineOverlap xOverlap := by simp
    _ =
        (xAffineOverlap * tAffineOverlap) *
          infinityOverlapToAffineOverlap xOverlap := by
            rw [xAffineOverlap_mul_tAffineOverlap]
    _ =
        xAffineOverlap *
          (tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap) := by
              rw [mul_assoc]
    _ = xAffineOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The forward overlap map sends `x⁻¹` back to `t`. -/
@[simp] theorem affineOverlapToInfinityOverlap_tAffineOverlap :
    affineOverlapToInfinityOverlap tAffineOverlap = tOverlap := by
  have hinv :
      xOverlap *
          affineOverlapToInfinityOverlap tAffineOverlap = 1 := by
    calc
      xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap =
          affineOverlapToInfinityOverlap xAffineOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap := by
              rw [affineOverlapToInfinityOverlap_xAffineOverlap]
      _ =
          affineOverlapToInfinityOverlap
            (xAffineOverlap * tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [xAffineOverlap_mul_tAffineOverlap, map_one]
  calc
    affineOverlapToInfinityOverlap tAffineOverlap =
        1 * affineOverlapToInfinityOverlap tAffineOverlap := by simp
    _ =
        (tOverlap * xOverlap) *
          affineOverlapToInfinityOverlap tAffineOverlap := by
            rw [tOverlap_mul_xOverlap]
    _ =
        tOverlap *
          (xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap) := by
              rw [mul_assoc]
    _ = tOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineOverlapToInfinityOverlap_yAffineOverlap :
    affineOverlapToInfinityOverlap yAffineOverlap =
      xOverlap ^ 3 * vOverlap := by
  rw [yAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_yClass]
  rfl
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse ordinary overlap map is a left inverse of the forward map. -/
theorem infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap :
    infinityOverlapToAffineOverlap.comp
        affineOverlapToInfinityOverlap =
      RingHom.id AffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        infinityOverlapToAffineOverlap
            (affineOverlapToInfinityOverlap xAffineOverlap) =
          xAffineOverlap
      simp
  · change
      infinityOverlapToAffineOverlap
          (affineOverlapToInfinityOverlap yAffineOverlap) =
        yAffineOverlap
    simp
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The forward ordinary overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13IntegralInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        affineOverlapToInfinityOverlap
            (infinityOverlapToAffineOverlap tOverlap) =
          tOverlap
      simp
  · change
      affineOverlapToInfinityOverlap
          (infinityOverlapToAffineOverlap vOverlap) =
        vOverlap
    simp
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The ordinary principal opens of the affine and infinity charts agree. -/
noncomputable def overlapEquiv :
    AffineOverlap ≃+* InfinityOverlap where
  toEquiv :=
    { toFun := affineOverlapToInfinityOverlap
      invFun := infinityOverlapToAffineOverlap
      left_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap z
      right_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap z }
  map_mul' := affineOverlapToInfinityOverlap.map_mul
  map_add' := affineOverlapToInfinityOverlap.map_add
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem pointU_on_overlap (P : IntegralInfinityPoint) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (xClassHom (pointU P)) =
      N13OrdinaryCurveOverlap.tOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 := by
  simp [pointU, xClassHom,
    N13OrdinaryCurveOverlap.tOverlap,
    N13IntegralInfinityChart.tClass,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem pointV_on_overlap (P : IntegralInfinityPoint) :
    (algebraMap InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap)
        (yClass - xClassHom (pointV P)) =
      N13OrdinaryCurveOverlap.vOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 := by
  simp [pointV, yClass, xClassHom,
    N13OrdinaryCurveOverlap.vOverlap,
    N13IntegralInfinityChart.vClass,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem affineU_on_overlap (P : IntegralInfinityPoint) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (affineU P)) =
      N13OrdinaryCurveOverlap.xOverlap *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap
            (xClassHom (pointU P))) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    pointU_on_overlap]
  simp only [affineU, map_sub, map_one, map_mul,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  rw [mul_sub, mul_comm N13OrdinaryCurveOverlap.xOverlap
      N13OrdinaryCurveOverlap.tOverlap,
    N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap]
  ring
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem affineV_on_overlap (P : IntegralInfinityPoint) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (GeneralizedGraphIdealCore.ySubClass
          N13GeneralizedMumfordIntegral.xClassHom
          N13GeneralizedMumfordIntegral.yClass
          (affineV P)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap
            (yClass - xClassHom (pointV P))) := by
  rw [pointV_on_overlap]
  simp only [GeneralizedGraphIdealCore.ySubClass, map_sub,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  simp [affineV,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  ring
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The two local point ideals agree on the ordinary overlap.  Their two
generators differ only by the units `x` and `x³`. -/
theorem pointIdeals_agree_on_overlap (P : IntegralInfinityPoint) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P) =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        (pointIdeal P) := by
  simp only [affinePointIdeal, pointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    Ideal.map_span, Set.image_pair]
  rw [affineU_on_overlap P, affineV_on_overlap P]
  let ux :
      N13OrdinaryCurveOverlap.InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hux3 :
      ((ux ^ 3 :
          N13OrdinaryCurveOverlap.InfinityOverlapˣ) :
        N13OrdinaryCurveOverlap.InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap ^ 3 := by
    change
      (ux : N13OrdinaryCurveOverlap.InfinityOverlap) ^ 3 =
        N13OrdinaryCurveOverlap.xOverlap ^ 3
    rw [hux]
  have hs :=
    span_pair_unit_mul
      ux (ux ^ 3)
      (algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap
          (xClassHom (pointU P)))
      (algebraMap InfinityCurve
        N13OrdinaryCurveOverlap.InfinityOverlap
          (yClass - xClassHom (pointV P)))
  rw [hux, hux3] at hs
  exact hs
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def infinityIdeal (D : GraphData) : Ideal InfinityCurve :=
  GeneralizedGraphIdealCore.graphIdeal
    N13IntegralInfinityGraphJacobian.xClassHom
    N13IntegralInfinityGraphJacobian.yClass
    D.u D.v
end
end MazurProof.N13IntegralInfinityGraphTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_curve_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem integralNormalPoly_eq (z : IntegralRing) :
    integralNormalPoly z =
      C (integralCoeff0 z) + C (integralCoeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ N13IntegralInfinityChart.infinityCurvePoly =
        C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0) +
          C ((g %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := N13IntegralInfinityChart.infinityCurvePoly)
        N13IntegralInfinityChart.infinityCurvePoly_monic
        (n := 2) (by rw [integral_curve_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Every ordinary element has a unique rank-two expression. -/
theorem integral_recompose (z : IntegralRing) :
    integralBaseClass (integralCoeff0 z) +
        integralBaseClass (integralCoeffV z) *
          N13IntegralInfinityChart.vClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        integralBaseClass (integralCoeff0 (AdjoinRoot.mk _ g)) +
              integralBaseClass (integralCoeffV (AdjoinRoot.mk _ g)) *
                N13IntegralInfinityChart.vClass =
            AdjoinRoot.mk _
              (C (integralCoeff0 (AdjoinRoot.mk _ g)) +
                C (integralCoeffV (AdjoinRoot.mk _ g)) * X) := by
                  simp only [integralBaseClass,
                    N13IntegralInfinityChart.vClass, map_add, map_mul,
                    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C,
                    AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk _ (integralNormalPoly (AdjoinRoot.mk _ g)) := by
              rw [integralNormalPoly_eq]
        _ = AdjoinRoot.mk _ g :=
          AdjoinRoot.mk_leftInverse
            N13IntegralInfinityChart.infinityCurvePoly_monic
            (AdjoinRoot.mk _ g)
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem graphEval_xClass
    (D : GraphData) (p : Base) :
    graphEval D
        (N13IntegralInfinityGraphJacobian.xClassHom p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p := by
  change graphEval D
      (AdjoinRoot.of
        N13IntegralInfinityChart.infinityCurvePoly p) = _
  exact AdjoinRoot.lift_of (graph_root_relation D)
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem graphEval_yClass
    (D : GraphData) :
    graphEval D N13IntegralInfinityGraphJacobian.yClass =
      Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base)) D.v :=
  AdjoinRoot.lift_root (graph_root_relation D)
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem graphEval_baseClass
    (D : GraphData) (p : Base) :
    graphEval D
        (N13IntegralInfinityReduction.integralBaseClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p := by
  change graphEval D
      (N13IntegralInfinityGraphJacobian.xClassHom p) = _
  exact graphEval_xClass D p
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem graphEval_vClass
    (D : GraphData) :
    graphEval D N13IntegralInfinityChart.vClass =
      Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base)) D.v := by
  change graphEval D N13IntegralInfinityGraphJacobian.yClass = _
  exact graphEval_yClass D
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem graphEval_ySubClass
    (D : GraphData) :
    graphEval D
        (GeneralizedGraphIdealCore.ySubClass
          N13IntegralInfinityGraphJacobian.xClassHom
          N13IntegralInfinityGraphJacobian.yClass D.v) = 0 := by
  simp [GeneralizedGraphIdealCore.ySubClass]
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityIdeal_le_ker
    (D : GraphData) :
    N13IntegralInfinityGraphTwoChart.infinityIdeal D ≤
      RingHom.ker (graphEval D) := by
  apply Ideal.span_le.mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change graphEval D
      (N13IntegralInfinityGraphJacobian.xClassHom D.u) = 0
    rw [graphEval_xClass, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  · exact graphEval_ySubClass D
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem ker_graphEval
    (D : GraphData) :
    RingHom.ker (graphEval D) =
      N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : Base :=
      N13IntegralInfinityReduction.integralCoeff0 z
    let q : Base :=
      N13IntegralInfinityReduction.integralCoeffV z
    have hz' :
        graphEval D
          (N13IntegralInfinityReduction.integralBaseClass p +
            N13IntegralInfinityReduction.integralBaseClass q *
              N13IntegralInfinityChart.vClass) = 0 := by
      rw [N13IntegralInfinityReduction.integral_recompose]
      exact hz
    have hquot :
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base))
          (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, graphEval_baseClass,
        graphEval_vClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu :
        N13IntegralInfinityGraphJacobian.xClassHom D.u ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      GeneralizedGraphIdealCore.xClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass D.u D.v
    have hv :
        GeneralizedGraphIdealCore.ySubClass
            N13IntegralInfinityGraphJacobian.xClassHom
            N13IntegralInfinityGraphJacobian.yClass D.v ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
        N13IntegralInfinityGraphJacobian.xClassHom
        N13IntegralInfinityGraphJacobian.yClass D.u D.v
    have hbase :
        N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
      rw [hs, map_mul, mul_comm]
      exact Ideal.mul_mem_left _ _ hu
    have hgraph :
        N13IntegralInfinityGraphJacobian.xClassHom q *
            GeneralizedGraphIdealCore.ySubClass
              N13IntegralInfinityGraphJacobian.xClassHom
              N13IntegralInfinityGraphJacobian.yClass D.v ∈
          N13IntegralInfinityGraphTwoChart.infinityIdeal D :=
      Ideal.mul_mem_left _ _ hv
    rw [← N13IntegralInfinityReduction.integral_recompose z]
    have hdecomp :
        N13IntegralInfinityReduction.integralBaseClass p +
            N13IntegralInfinityReduction.integralBaseClass q *
              N13IntegralInfinityChart.vClass =
          N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              GeneralizedGraphIdealCore.ySubClass
                N13IntegralInfinityGraphJacobian.xClassHom
                N13IntegralInfinityGraphJacobian.yClass D.v := by
      change
        N13IntegralInfinityGraphJacobian.xClassHom p +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              N13IntegralInfinityGraphJacobian.yClass =
          N13IntegralInfinityGraphJacobian.xClassHom (p + q * D.v) +
            N13IntegralInfinityGraphJacobian.xClassHom q *
              (N13IntegralInfinityGraphJacobian.yClass -
                N13IntegralInfinityGraphJacobian.xClassHom D.v)
      simp only [map_add, map_mul]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact infinityIdeal_le_ker D
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A monic infinity graph ideal is saturated with respect to every
nonzero scalar from the two-adic base. -/
theorem infinityIdeal_scalarSaturated
    (D : GraphData)
    (hu : D.u.Monic)
    (r : R₂) (hr : r ≠ 0)
    (z : InfinityCurve)
    (hz :
      algebraMap R₂ InfinityCurve r * z ∈
        N13IntegralInfinityGraphTwoChart.infinityIdeal D) :
    z ∈ N13IntegralInfinityGraphTwoChart.infinityIdeal D := by
  letI : Module.Free R₂ (GraphResidue D) :=
    hu.free_quotient
  have hker :
      algebraMap R₂ InfinityCurve r * z ∈
        RingHom.ker (graphEval D) := by
    rw [ker_graphEval]
    exact hz
  have hmap :
      graphEval D (algebraMap R₂ InfinityCurve r * z) = 0 :=
    hker
  have hscalar :
      r • graphEval D z =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (C r) *
          graphEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (graphEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set Base)) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set Base))).map_mul (C r) p
  have hsmul : r • graphEval D z = 0 := by
    rw [hscalar]
    have hscalarMap :
        graphEval D (algebraMap R₂ InfinityCurve r) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set Base)) (C r) := by
      change graphEval D
        (N13IntegralInfinityGraphJacobian.xClassHom (C r)) = _
      exact graphEval_xClass D (C r)
    simpa only [map_mul, hscalarMap] using hmap
  have heval : graphEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_graphEval D, RingHom.mem_ker]
  exact heval
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
/-- Saturation by base scalars is preserved when an ordinary ring is
localized in a horizontal element. -/
theorem scalarSaturated_map_localization
    {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    (M : Submonoid S)
    [IsLocalization M T]
    {I : Ideal S}
    (hI :
      ∀ (r : R), r ≠ 0 → ∀ z : S,
        algebraMap R S r * z ∈ I → z ∈ I) :
    ∀ (r : R), r ≠ 0 → ∀ z : T,
      algebraMap R T r * z ∈
          Ideal.map (algebraMap S T) I →
        z ∈ Ideal.map (algebraMap S T) I := by
  intro r hr z hz
  obtain ⟨⟨a, s⟩, hzs⟩ :=
    IsLocalization.surj M z
  let J : Ideal T :=
    Ideal.map (algebraMap S T) I
  have hraMap :
      algebraMap S T (algebraMap R S r * a) ∈ J := by
    have hmul :
        algebraMap S T (s : S) *
            (algebraMap R T r * z) ∈ J :=
      Ideal.mul_mem_left J _ hz
    have heq :
        algebraMap S T (algebraMap R S r * a) =
          algebraMap S T (s : S) *
            (algebraMap R T r * z) := by
      rw [map_mul, IsScalarTower.algebraMap_apply R S T, ← hzs]
      ring
    rw [heq]
    exact hmul
  have hraDenom :
      ∃ q ∈ M, (q : S) * (algebraMap R S r * a) ∈ I := by
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hraMap
    exact hraMap
  obtain ⟨q, hq, hqra⟩ := hraDenom
  have hqa : (q : S) * a ∈ I := by
    apply hI r hr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hqra
  have hqaMap :
      algebraMap S T ((q : S) * a) ∈ J :=
    Ideal.mem_map_of_mem (algebraMap S T) hqa
  have haMap : algebraMap S T a ∈ J := by
    apply
      (Ideal.unit_mul_mem_iff_mem J
        (IsLocalization.map_units T ⟨q, hq⟩)).mp
    simpa only [map_mul] using hqaMap
  have hzsMem :
      z * algebraMap S T (s : S) ∈ J := by
    rw [hzs]
    exact haMap
  apply
    (Ideal.unit_mul_mem_iff_mem J
      (IsLocalization.map_units T s)).mp
  simpa only [mul_comm] using hzsMem
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem mem_of_x_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := hx
  have h₁ := Ideal.mul_mem_left I z hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1 <;> ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem mem_of_x_pow_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    (n : ℕ) {z : AffineCurve}
    (hz : N13OrdinaryCurveOverlap.xClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_x_mul_mem hx
      convert hz using 1 <;> simp only [pow_succ] <;> ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Localizing at `x` loses no ideal information when `x` is already a
unit modulo the ideal. -/
theorem comap_map_affineOverlap_eq_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap)
        (Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z ∈
        Ideal.map
          (algebraMap AffineCurve
            N13OrdinaryCurveOverlap.AffineOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_x_pow_mul_mem hx n hmz
  · exact Ideal.le_comap_map
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The actual affine-to-infinity overlap map is the localization map
followed by the chart equivalence. -/
private theorem affineToInfinityOverlap_eq_comp :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13OrdinaryCurveOverlap.overlapEquiv.toRingHom.comp
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap) := by
  apply DFunLike.ext _ _
  intro z
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap z =
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap AffineCurve
          N13OrdinaryCurveOverlap.AffineOverlap z)
  exact
    (N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap
      z).symm
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction to the actual ordinary overlap loses no information from
an affine ideal when `x` is already a unit modulo that ideal. -/
theorem affineOverlapContracted_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I) =
      I := by
  let loc :
      AffineCurve →+*
        N13OrdinaryCurveOverlap.AffineOverlap :=
    algebraMap AffineCurve
      N13OrdinaryCurveOverlap.AffineOverlap
  let e :
      N13OrdinaryCurveOverlap.AffineOverlap →+*
        InfinityOverlap :=
    N13OrdinaryCurveOverlap.overlapEquiv.toRingHom
  have he :
      Ideal.comap e (Ideal.map e (Ideal.map loc I)) =
        Ideal.map loc I := by
    rw [Ideal.comap_map_of_surjective e
      N13OrdinaryCurveOverlap.overlapEquiv.surjective]
    have hker : RingHom.ker e = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e).mp
        N13OrdinaryCurveOverlap.overlapEquiv.injective
    rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq]
  rw [affineToInfinityOverlap_eq_comp,
    ← Ideal.map_map, ← Ideal.comap_comap, he]
  exact comap_map_affineOverlap_eq_of_xUnitMod hx
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_algebraMap_R₂
    (r : R₂) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (algebraMap R₂ AffineCurve r) =
      algebraMap R₂ InfinityOverlap r := by
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (C r)) =
      _
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13OrdinaryCurveOverlap.affineCoeffMap_C]
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r
  exact IsScalarTower.algebraMap_apply R₂ InfinityCurve InfinityOverlap r
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The cleared horizontal equation of an integral infinity-chart point
makes the ordinary affine coordinate invertible modulo its affine point
ideal.  This prevents localization at that coordinate from losing an
affine-chart component. -/
theorem affinePointIdeal_xUnitMod
    (P : N13IntegralInfinityPointSpread.IntegralInfinityPoint) :
    N13IntegralInfinityGraphSaturation.XUnitMod
      (N13IntegralInfinityPointSpread.affinePointIdeal P) := by
  let q : N13IntegralModelContraction.IntegralRing :=
    N13GeneralizedMumfordIntegral.xClassHom
      (Polynomial.C P.1.1)
  refine ⟨q, ?_⟩
  have hgen :
      N13GeneralizedMumfordIntegral.xClassHom
          (N13IntegralInfinityPointSpread.affineU P) ∈
        N13IntegralInfinityPointSpread.affinePointIdeal P :=
    GeneralizedGraphIdealCore.xClass_mem_graphIdeal
      N13GeneralizedMumfordIntegral.xClassHom
      N13GeneralizedMumfordIntegral.yClass
      (N13IntegralInfinityPointSpread.affineU P)
      (N13IntegralInfinityPointSpread.affineV P)
  change
    1 - q * N13OrdinaryCurveOverlap.xClass ∈
      N13IntegralInfinityPointSpread.affinePointIdeal P
  simpa only [q, N13IntegralInfinityPointSpread.affineU,
    N13OrdinaryCurveOverlap.xClass,
    N13GeneralizedMumfordIntegral.xClassHom_apply,
    map_sub, map_mul, map_one] using hgen
end
end MazurProof.N13EscapingPointPicardRealization
end
end

attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution (P : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (r : N13IntegralModelContraction.R₂) (hr : r ≠ 0) (z : N13IntegralModelContraction.IntegralRing) (hz : algebraMap N13IntegralModelContraction.R₂ N13IntegralModelContraction.IntegralRing r * z ∈ N13IntegralInfinityPointSpread.affinePointIdeal P) : z ∈ N13IntegralInfinityPointSpread.affinePointIdeal P := by
  let Ia := N13IntegralInfinityPointSpread.affinePointIdeal P
  let Ii := N13IntegralInfinityPointSpread.pointIdeal P
  let f := N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g :
      N13IntegralInfinityPointSpread.InfinityCurve →+*
        N13OrdinaryCurveOverlap.InfinityOverlap :=
    algebraMap
      N13IntegralInfinityPointSpread.InfinityCurve
      N13OrdinaryCurveOverlap.InfinityOverlap
  have hoverlap : Ideal.map f Ia = Ideal.map g Ii := by
    exact N13IntegralInfinityPointSpread.pointIdeals_agree_on_overlap P
  have hInfinity :
      ∀ (s : N13IntegralModelContraction.R₂), s ≠ 0 →
        ∀ w : N13IntegralInfinityPointSpread.InfinityCurve,
          algebraMap N13IntegralModelContraction.R₂
                N13IntegralInfinityPointSpread.InfinityCurve s * w ∈ Ii →
            w ∈ Ii := by
    intro s hs w hw
    change
      algebraMap N13IntegralModelContraction.R₂
            N13IntegralInfinityPointSpread.InfinityCurve s * w ∈
        N13IntegralInfinityGraphTwoChart.infinityIdeal
          (N13IntegralInfinityPointSpread.pointSemiGraph P) at hw
    change
      w ∈ N13IntegralInfinityGraphTwoChart.infinityIdeal
        (N13IntegralInfinityPointSpread.pointSemiGraph P)
    exact
      N13IntegralInfinityGraphSaturation.infinityIdeal_scalarSaturated
        (N13IntegralInfinityPointSpread.pointSemiGraph P)
        (Polynomial.monic_X_sub_C P.1.1)
        s hs w hw
  have hInfinityOverlap :
      ∀ (s : N13IntegralModelContraction.R₂), s ≠ 0 →
        ∀ w : N13OrdinaryCurveOverlap.InfinityOverlap,
          algebraMap N13IntegralModelContraction.R₂
                N13OrdinaryCurveOverlap.InfinityOverlap s * w ∈
              Ideal.map g Ii →
            w ∈ Ideal.map g Ii := by
    exact
      N13IntegralInfinityGraphSaturation.scalarSaturated_map_localization
        (R := N13IntegralModelContraction.R₂)
        (S := N13IntegralInfinityPointSpread.InfinityCurve)
        (T := N13OrdinaryCurveOverlap.InfinityOverlap)
        (Submonoid.powers N13IntegralInfinityChart.tClass)
        hInfinity
  have hrzOverlap :
      algebraMap N13IntegralModelContraction.R₂
            N13OrdinaryCurveOverlap.InfinityOverlap r * f z ∈
        Ideal.map g Ii := by
    rw [← hoverlap]
    have hm := Ideal.mem_map_of_mem f hz
    simpa only [f, Ia, map_mul,
      N13IntegralInfinityGraphSaturation.affineToInfinityOverlap_algebraMap_R₂]
      using hm
  have hzOverlap : f z ∈ Ideal.map g Ii :=
    hInfinityOverlap r hr (f z) hrzOverlap
  have hzComap : z ∈ Ideal.comap f (Ideal.map f Ia) := by
    change f z ∈ Ideal.map f Ia
    rw [hoverlap]
    exact hzOverlap
  rw [N13IntegralInfinityGraphSaturation.affineOverlapContracted_of_xUnitMod
    (affinePointIdeal_xUnitMod P)] at hzComap
  exact hzComap
