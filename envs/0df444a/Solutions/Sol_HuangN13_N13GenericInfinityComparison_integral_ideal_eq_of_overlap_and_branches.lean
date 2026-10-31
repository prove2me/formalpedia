-- Prove2me | solution 1 for HuangN13.N13GenericInfinityComparison.integral_ideal_eq_of_overlap_and_branches
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:08:37.416323+00:00
-- url     : https://prove2.me/submissions/b5d4fdce-7318-4959-a1a2-20aebc87a354

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)
end
end MazurProof.N13GeneralizedMumfordReduction
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
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
instance infinityOverlap_isDomain : IsDomain InfinityOverlap :=
  N13OrdinaryCurveOverlap.overlapEquiv.symm.toMulEquiv.isDomain
    AffineOverlap
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_powers_le_nonZeroDivisors :
    Submonoid.powers N13IntegralInfinityChart.tClass ≤
      nonZeroDivisors InfinityCurve :=
  Submonoid.powers_le.mpr
    infinity_tClass_mem_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_to_overlap_injective :
    Function.Injective
      (algebraMap InfinityCurve InfinityOverlap) :=
  IsLocalization.injective InfinityOverlap
    infinity_powers_le_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
instance infinityCurve_isDomain : IsDomain InfinityCurve :=
  infinity_to_overlap_injective.isDomain
    (algebraMap InfinityCurve InfinityOverlap)
end
end MazurProof.N13IntegralCurveProperties
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurvePoly_degree :
    N13IntegralInfinityChart.infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13IntegralInfinityChart.infinityCurvePoly_monic.ne_zero,
    N13IntegralInfinityChart.infinityCurvePoly_natDegree]
  norm_num
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem xClassHom_injective :
    Function.Injective xClassHom := by
  exact
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [infinityCurvePoly_degree]; norm_num)
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
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  exact N13GeneralizedMumfordReduction.reduceBase_two
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
@[simp] theorem reduce_vClass :
    reduceCoordinate N13IntegralInfinityChart.vClass =
      N13SpecialInfinityChart.vClass := by
  exact AdjoinRoot.map_root
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralBaseClass (p : IntegralBase) :
    reduceCoordinate (integralBaseClass p) =
      specialBaseClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd p
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
private theorem special_curve_degree :
    N13SpecialInfinityChart.curvePoly.degree = 2 := by
  rw [degree_eq_natDegree
      N13SpecialInfinityChart.curvePoly_monic.ne_zero,
    N13SpecialInfinityChart.curvePoly_natDegree]
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
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass (p : SpecialBase) :
    specialCoeff0 (specialBaseClass p) = p := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass (p : SpecialBase) :
    specialCoeffV (specialBaseClass p) = 0 := by
  change
    (C p %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [special_curve_degree]
      norm_num)
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_vClass :
    specialCoeff0 N13SpecialInfinityChart.vClass = 0 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_vClass :
    specialCoeffV N13SpecialInfinityChart.vClass = 1 := by
  change (X %ₘ N13SpecialInfinityChart.curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff
      N13SpecialInfinityChart.curvePoly_monic).mpr]
  · simp
  · rw [degree_X, special_curve_degree]
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeff0_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeff0
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = 0 := by
  change specialCoeff0
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = 0
  rw [← Algebra.smul_def]
  simp
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
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem specialCoeffV_baseClass_mul_vClass
    (p : SpecialBase) :
    specialCoeffV
        (specialBaseClass p * N13SpecialInfinityChart.vClass) = p := by
  change specialCoeffV
    ((algebraMap SpecialBase SpecialRing p) *
      N13SpecialInfinityChart.vClass) = p
  rw [← Algebra.smul_def]
  simp
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reduction is coefficientwise in the rank-two bases. -/
@[simp] theorem reduce_integralCoeff0 (z : IntegralRing) :
    specialCoeff0 (reduceCoordinate z) =
      reducePoly (integralCoeff0 z) := by
  calc
    specialCoeff0 (reduceCoordinate z) =
        specialCoeff0
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeff0 z) := by
      simp
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralCoeffV (z : IntegralRing) :
    specialCoeffV (reduceCoordinate z) =
      reducePoly (integralCoeffV z) := by
  calc
    specialCoeffV (reduceCoordinate z) =
        specialCoeffV
          (reduceCoordinate
            (integralBaseClass (integralCoeff0 z) +
              integralBaseClass (integralCoeffV z) *
                N13IntegralInfinityChart.vClass)) := by
          rw [integral_recompose]
    _ = reducePoly (integralCoeffV z) := by
      simp
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : IntegralBase) (hp : reducePoly p = 0) :
    ∃ q : IntegralBase, p = C (2 : R₂) * q := by
  have hmem : p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reduction has exactly the vertical principal ideal `(2)` as kernel. -/
theorem ker_reduceCoordinate :
    RingHom.ker reduceCoordinate =
      Ideal.span
        ({algebraMap R₂ IntegralRing (2 : R₂)} :
          Set IntegralRing) := by
  apply le_antisymm
  · intro z hz
    have hz0 : reduceCoordinate z = 0 :=
      RingHom.mem_ker.mp hz
    have h0 :
        reducePoly (integralCoeff0 z) = 0 := by
      rw [← reduce_integralCoeff0 z, hz0]
      simp
    have hV :
        reducePoly (integralCoeffV z) = 0 := by
      rw [← reduce_integralCoeffV z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hV
    rw [Ideal.mem_span_singleton]
    refine ⟨
      integralBaseClass p +
        integralBaseClass q * N13IntegralInfinityChart.vClass,
      ?_⟩
    rw [← integral_recompose z, hp, hq]
    calc
      integralBaseClass (C 2 * p) +
            integralBaseClass (C 2 * q) *
              N13IntegralInfinityChart.vClass =
          integralBaseClass (C 2) *
            (integralBaseClass p +
                integralBaseClass q *
                  N13IntegralInfinityChart.vClass) := by
            simp only [integralBaseClass, map_mul, mul_add]
            ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
            (integralBaseClass p +
              integralBaseClass q *
                N13IntegralInfinityChart.vClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate (integralBaseClass (C (2 : R₂))) = 0
    rw [reduce_integralBaseClass]
    simp [reducePoly, specialBaseClass]
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_mem_xIdeal :
    branchZero ∈ xIdeal :=
  (Classical.choose_spec exists_branch_zero).2
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_constantCoeff :
    PowerSeries.constantCoeff branchZero = 0 := by
  have hle :
      xIdeal ≤ RingHom.ker
        (PowerSeries.constantCoeff : Power →+* R₂) := by
    rw [xIdeal, Ideal.span_le]
    intro z hz
    subst z
    exact RingHom.mem_ker.mpr PowerSeries.constantCoeff_X
  exact RingHom.mem_ker.mp (hle branchZero_mem_xIdeal)
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchOne_constantCoeff :
    PowerSeries.constantCoeff branchOne = -1 := by
  simp [branchOne, branchZero_constantCoeff,
    N13FormalInfinityChart.hPower]
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branch_difference_constantCoeff :
    PowerSeries.constantCoeff (branchZero - branchOne) = 1 := by
  simp [branchZero_constantCoeff, branchOne_constantCoeff]
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The two lifted branches remain disjoint over the complete base. -/
theorem branch_difference_isUnit :
    IsUnit (branchZero - branchOne) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    branch_difference_constantCoeff]
  exact isUnit_one
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_of
    (f : Power) :
    evalBranchZero
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_of
    (f : Power) :
    evalBranchOne
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_vClass :
    evalBranchZero N13FormalInfinityChart.vClass =
      branchZero := by
  exact AdjoinRoot.lift_root eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_vClass :
    evalBranchOne N13FormalInfinityChart.vClass =
      branchOne := by
  exact AdjoinRoot.lift_root eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The unit represented by the difference of the two branches. -/
def branchDifferenceUnit : Powerˣ :=
  branch_difference_isUnit.unit
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem branchDifferenceUnit_coe :
    (branchDifferenceUnit : Power) =
      branchZero - branchOne :=
  IsUnit.unit_spec branch_difference_isUnit
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem coeffMap_injective :
    Function.Injective coeffMap :=
  IsFractionRing.injective R₂ Q₂
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
abbrev plus := N13InfinityChartMarking.positiveIntegralExpansion
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
abbrev minus := N13InfinityChartMarking.negativeIntegralExpansion
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
abbrev r₀ := N13FormalInfinityBranches.branchZero
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
abbrev r₁ := N13FormalInfinityBranches.branchOne
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_base (p : R₂[X]) : plus (base p) = beta p := by
  simp [plus, base, N13InfinityChartMarking.positiveIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchZero]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_base (p : R₂[X]) : minus (base p) = beta p := by
  simp [minus, base, N13InfinityChartMarking.negativeIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchOne]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_v : plus N13IntegralInfinityChart.vClass = r₀ := by
  simp [plus, N13InfinityChartMarking.positiveIntegralExpansion]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_v : minus N13IntegralInfinityChart.vClass = r₁ := by
  simp [minus, N13InfinityChartMarking.negativeIntegralExpansion]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem plus_normal_form (z : B) :
    plus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₀ := by
  calc
    plus z = plus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg plus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, plus_base, plus_base, plus_v]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem minus_normal_form (z : B) :
    minus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₁ := by
  calc
    minus z = minus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg minus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, minus_base, minus_base, minus_v]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem polynomial_dvd_of_beta_dvd (p : R₂[X]) (n : ℕ)
    (h : (PowerSeries.X : P) ^ n ∣ beta p) : (X : R₂[X]) ^ n ∣ p := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  have hh := PowerSeries.X_pow_dvd_iff.mp h i hi
  simpa only [beta_eq_coe, Polynomial.coeff_coe] using hh
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Both actual integral branch jets detect the t-adic kernel on the
ordinary chart, by its rank-two normal form and the unit root difference. -/
theorem integral_branch_dvd_iff (z : B) (n : ℕ) :
    N13IntegralInfinityChart.tClass ^ n ∣ z ↔
      (PowerSeries.X : P) ^ n ∣ plus z ∧ (PowerSeries.X : P) ^ n ∣ minus z := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨plus w, ?_⟩
      simp [plus, N13InfinityChartMarking.positiveIntegralExpansion]
    · refine ⟨minus w, ?_⟩
      simp [minus, N13InfinityChartMarking.negativeIntegralExpansion]
  · rintro ⟨hp, hm⟩
    rw [plus_normal_form] at hp
    rw [minus_normal_form] at hm
    let u := N13IntegralInfinityReduction.integralCoeff0 z
    let v := N13IntegralInfinityReduction.integralCoeffV z
    have hdiff : (PowerSeries.X : P) ^ n ∣ beta v * (r₀ - r₁) := by
      convert dvd_sub hp hm using 1 <;> dsimp [u, v] <;> ring
    have hv : (PowerSeries.X : P) ^ n ∣ beta v := by
      obtain ⟨w, hw⟩ := N13FormalInfinityBranches.branch_difference_isUnit
      rw [← hw] at hdiff
      obtain ⟨c, hc⟩ := hdiff
      refine ⟨c * (↑(w⁻¹) : P), ?_⟩
      calc
        beta v = (beta v * (w : P)) * (↑(w⁻¹) : P) := by simp [mul_assoc]
        _ = (PowerSeries.X : P) ^ n * (c * (↑(w⁻¹) : P)) := by rw [hc]; ring
    have hu : (PowerSeries.X : P) ^ n ∣ beta u := by
      have hvm : (PowerSeries.X : P) ^ n ∣ beta v * r₀ :=
        hv.trans (dvd_mul_right _ _)
      have h := dvd_sub hp hvm
      simpa only [u, v, add_sub_cancel_right] using h
    obtain ⟨a, ha⟩ := polynomial_dvd_of_beta_dvd u n hu
    obtain ⟨b, hb⟩ := polynomial_dvd_of_beta_dvd v n hv
    refine ⟨base a + base b * N13IntegralInfinityChart.vClass, ?_⟩
    calc
      z = base u + base v * N13IntegralInfinityChart.vClass :=
        (N13IntegralInfinityReduction.integral_recompose z).symm
      _ = base ((X : R₂[X]) ^ n * a) +
          base ((X : R₂[X]) ^ n * b) * N13IntegralInfinityChart.vClass := by rw [ha, hb]
      _ = N13IntegralInfinityChart.tClass ^ n *
          (base a + base b * N13IntegralInfinityChart.vClass) := by
        simp only [base, N13IntegralInfinityReduction.integralBaseClass, map_mul, map_pow]
        change N13IntegralInfinityChart.tClass ^ n * base a +
          (N13IntegralInfinityChart.tClass ^ n * base b) * N13IntegralInfinityChart.vClass = _
        simp only [base, N13IntegralInfinityReduction.integralBaseClass]
        ring
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem powerMap_reflects_X_pow_dvd (f : P) (n : ℕ) :
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap f ↔
      (PowerSeries.X : P) ^ n ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h i hi
    have hh := h i hi
    rw [N13TwoAdicInfinityCompatibility.powerMap_coeff] at hh
    apply N13TwoAdicInfinityCompatibility.coeffMap_injective
    simpa only [map_zero] using hh
  · intro h i hi
    rw [N13TwoAdicInfinityCompatibility.powerMap_coeff, h i hi, map_zero]
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The SAME finite-jet kernel is detected by the generic branch maps used
in HasInfinityMultiplicities. Coefficient injection prevents losing a
nonzero low-order term when passing from Z2 to Q2. -/
theorem generic_branch_dvd_iff (z : B) (n : ℕ) :
    N13IntegralInfinityChart.tClass ^ n ∣ z ↔
      (PowerSeries.X : QP) ^ n ∣ N13InfinityChartMarking.positiveExpansion z ∧
      (PowerSeries.X : QP) ^ n ∣ N13InfinityChartMarking.negativeExpansion z := by
  change N13IntegralInfinityChart.tClass ^ n ∣ z ↔
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap (plus z) ∧
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap (minus z)
  rw [powerMap_reflects_X_pow_dvd, powerMap_reflects_X_pow_dvd]
  exact integral_branch_dvd_iff z n
end
end MazurProof.N13InfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InvertibleReductionSaturation
noncomputable section
open scoped nonZeroDivisors
section General
variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [CommRing S] [IsDomain S]
/-- Invertibility lets us test membership after multiplication by every
inverse-ideal section. Reduction modulo the kernel generator cancels the
nonzero reduction of one ideal section, and forces the apparent denominator
to divide. This removes one vertical factor. -/
theorem kernel_generator_saturated
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) :
    ∀ x : A, p * x ∈ I → x ∈ I := by
  classical
  have hex : ∃ a : A, a ∈ I ∧ red a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hred
    apply (Ideal.map_eq_bot_iff_le_ker red).mpr
    intro a ha
    exact RingHom.mem_ker.mpr (h a ha)
  obtain ⟨a, ha, hared⟩ := hex
  have hpred : red p = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton p)
  let U : (FractionalIdeal A⁰ K)ˣ := hI.unit
  have hU : (U : FractionalIdeal A⁰ K) = (I : FractionalIdeal A⁰ K) := hI.unit_spec
  have hUI : (↑U⁻¹ : FractionalIdeal A⁰ K) * (I : FractionalIdeal A⁰ K) = 1 := by
    rw [← hU]
    exact Units.inv_mul U
  have hIU : (I : FractionalIdeal A⁰ K) * (↑U⁻¹ : FractionalIdeal A⁰ K) = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  intro x hpx
  have hInvSpan :
      (↑U⁻¹ : FractionalIdeal A⁰ K) *
        FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) ≤ 1 := by
    rw [mul_comm, FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have hcz : z * algebraMap A K (p * x) ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← hUI]
      exact FractionalIdeal.mul_mem_mul hz (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hpx)
    have hdz : z * algebraMap A K a ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← hUI]
      exact FractionalIdeal.mul_mem_mul hz (FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha)
    have hcTop : z * algebraMap A K (p * x) ∈ ((⊤ : Ideal A) : FractionalIdeal A⁰ K) := by
      simpa using hcz
    have hdTop : z * algebraMap A K a ∈ ((⊤ : Ideal A) : FractionalIdeal A⁰ K) := by
      simpa using hdz
    obtain ⟨c, _, hc⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hcTop
    obtain ⟨d, _, hd⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hdTop
    have hpc : p * (d * x) = a * c := by
      apply IsFractionRing.injective A K
      simp only [map_mul]
      rw [hc, hd, map_mul]
      ring
    have hcRed : red c = 0 := by
      have heq := congrArg red hpc
      have hz' : red a * red c = 0 := by
        simpa only [map_mul, hpred, zero_mul] using heq.symm
      exact (mul_eq_zero.mp hz').resolve_left hared
    have hcDiv : p ∣ c := by
      have hcKer : c ∈ RingHom.ker red := RingHom.mem_ker.mpr hcRed
      rwa [hker, Ideal.mem_span_singleton] at hcKer
    obtain ⟨e, he⟩ := hcDiv
    have hpK : algebraMap A K p ≠ 0 := by
      intro hz'
      apply hp
      apply IsFractionRing.injective A K
      simpa using hz'
    have hzx : z * algebraMap A K x = algebraMap A K e := by
      apply mul_left_cancel₀ hpK
      calc
        algebraMap A K p * (z * algebraMap A K x) = algebraMap A K c := by
          rw [hc, map_mul]
          ring
        _ = algebraMap A K p * algebraMap A K e := by rw [he, map_mul]
    have heOne : algebraMap A K e ∈ (1 : FractionalIdeal A⁰ K) := by
      simpa using (FractionalIdeal.mem_coeIdeal_of_mem A⁰
        (show e ∈ (⊤ : Ideal A) from Ideal.mem_top))
    rw [mul_comm, hzx]
    exact heOne
  have hspan : FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) ≤
      (I : FractionalIdeal A⁰ K) := by
    calc
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) =
          ((I : FractionalIdeal A⁰ K) * (↑U⁻¹ : FractionalIdeal A⁰ K)) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K x) := by rw [hIU, one_mul]
      _ = (I : FractionalIdeal A⁰ K) *
          ((↑U⁻¹ : FractionalIdeal A⁰ K) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K x)) := by rw [mul_assoc]
      _ ≤ (I : FractionalIdeal A⁰ K) * 1 :=
        mul_le_mul_right hInvSpan (I : FractionalIdeal A⁰ K)
      _ = (I : FractionalIdeal A⁰ K) := mul_one _
  have hxFrac : algebraMap A K x ∈ (I : FractionalIdeal A⁰ K) :=
    hspan (FractionalIdeal.mem_spanSingleton_self A⁰ (algebraMap A K x))
  obtain ⟨b, hb, hbx⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hxFrac
  have hbx' : b = x := (IsFractionRing.injective A K) hbx
  simpa [hbx'] using hb
end General
end
end MazurProof.N13InvertibleReductionSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InvertibleReductionSaturation
noncomputable section
open scoped nonZeroDivisors
section General
variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [CommRing S] [IsDomain S]
theorem kernel_generator_pow_saturated
    (red : A →+* S) (p : A) (hp : p ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) (n : ℕ) :
    ∀ x : A, p ^ n * x ∈ I → x ∈ I := by
  induction n with
  | zero =>
    intro x hx
    simpa using hx
  | succ n ih =>
    intro x hx
    apply ih x
    apply kernel_generator_saturated red p hp hker I hI hred
    simpa only [pow_succ', mul_assoc] using hx
end General
end
end MazurProof.N13InvertibleReductionSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InvertibleReductionSaturation
noncomputable section
open scoped nonZeroDivisors
section TwoAdic
variable {A K S : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Algebra R₂ A]
  [CommRing S] [IsDomain S]
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Unit-times-power decomposition in Z2 extends one-factor saturation to
cancellation of every nonzero base scalar. -/
theorem twoAdic_scalar_saturated_of_reduction_ne_bot
    (red : A →+* S)
    (h2 : algebraMap R₂ A (2 : R₂) ≠ 0)
    (hker : RingHom.ker red = Ideal.span ({algebraMap R₂ A (2 : R₂)} : Set A))
    (I : Ideal A) (hI : IsUnit (I : FractionalIdeal A⁰ K))
    (hred : Ideal.map red I ≠ ⊥) :
    ∀ r : R₂, r ≠ 0 → ∀ x : A, algebraMap R₂ A r * x ∈ I → x ∈ I := by
  intro r hr x hx
  have hu : IsUnit (algebraMap R₂ A (PadicInt.unitCoeff hr : R₂)) :=
    (PadicInt.unitCoeff hr).isUnit.map (algebraMap R₂ A)
  rw [PadicInt.unitCoeff_spec hr, map_mul, map_pow] at hx
  have hxpow : (algebraMap R₂ A (2 : R₂)) ^ r.valuation * x ∈ I := by
    apply (I.mul_unit_mem_iff_mem hu).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm, RingHom.map_one,
      Int.cast_ofNat, Nat.cast_two] using hx
  exact kernel_generator_pow_saturated red _ h2 hker I hI hred r.valuation x hxpow
end TwoAdic
end
end MazurProof.N13InvertibleReductionSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InvertibleReductionSaturation
noncomputable section
open scoped nonZeroDivisors
section InfinityApplication
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinity_two_ne_zero : algebraMap R₂ B (2 : R₂) ≠ 0 := by
  intro hz
  have hh : N13IntegralInfinityPointSpread.xClassHom (C (2 : R₂)) =
      N13IntegralInfinityPointSpread.xClassHom 0 := by
    have hmap : N13IntegralInfinityPointSpread.xClassHom (C (2 : R₂)) =
        algebraMap R₂ B (2 : R₂) := by
      simp [N13IntegralInfinityPointSpread.xClassHom]
      rfl
    rw [hmap, hz, map_zero]
  have hc := N13IntegralInfinityPointSpread.xClassHom_injective hh
  have hcc := congrArg (fun p : R₂[X] => p.coeff 0) hc
  norm_num at hcc
end InfinityApplication
end
end MazurProof.N13InvertibleReductionSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
abbrev r₀q := N13TwoAdicInfinityCompatibility.powerMap r₀
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
abbrev r₁q := N13TwoAdicInfinityCompatibility.powerMap r₁
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def differenceUnit : QPˣ :=
  Units.map N13TwoAdicInfinityCompatibility.powerMap.toMonoidHom
    N13FormalInfinitySplit.branchDifferenceUnit
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem differenceUnit_coe : (differenceUnit : QP) = r₀q - r₁q := by
  change N13TwoAdicInfinityCompatibility.powerMap
      (N13FormalInfinitySplit.branchDifferenceUnit : P) = _
  rw [N13FormalInfinitySplit.branchDifferenceUnit_coe, map_sub]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem inverse_difference_mul : (↑(differenceUnit⁻¹) : QP) * (r₀q - r₁q) = 1 := by
  rw [← differenceUnit_coe]
  exact Units.inv_mul differenceUnit
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def interpolationV (r s : QP) : QP := (r - s) * (↑(differenceUnit⁻¹) : QP)
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def interpolationU (r s : QP) : QP := r - interpolationV r s * r₀q
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem interpolation_plus (r s : QP) :
    interpolationU r s + interpolationV r s * r₀q = r := by
  unfold interpolationU
  ring
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem interpolation_minus (r s : QP) :
    interpolationU r s + interpolationV r s * r₁q = s := by
  calc
    interpolationU r s + interpolationV r s * r₁q =
        r - interpolationV r s * (r₀q - r₁q) := by unfold interpolationU; ring
    _ = r - (r - s) := by
      rw [interpolationV, mul_assoc, inverse_difference_mul, mul_one]
    _ = s := by ring
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13InfinityBranchJetLift.instAlgebraPolynomialR₂Q₂ MazurProof.N13InfinityBranchJetLift.instIsLocalizationPolynomialR₂MapMonoidHomCNonZeroDivisorsQ₂
theorem clear_two_polynomials (p q : Q₂[X]) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ a b : R₂[X],
      p * C (cMap c) = a.map cMap ∧ q * C (cMap c) = b.map cMap := by
  obtain ⟨a, b, d, hp, hq⟩ := IsLocalization.surj₂
    ((nonZeroDivisors R₂).map (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom) Q₂[X] p q
  obtain ⟨c, hc, hd⟩ := d.property
  change C c = (d : R₂[X]) at hd
  rw [← hd] at hp hq
  rw [Polynomial.algebraMap_def] at hp hq
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp hc, a, b, ?_, ?_⟩
  · change p * C (algebraMap R₂ Q₂ c) = a.map (algebraMap R₂ Q₂)
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using hp
  · change q * C (algebraMap R₂ Q₂ c) = b.map (algebraMap R₂ Q₂)
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using hq
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem generic_plus_base (p : R₂[X]) :
    N13InfinityChartMarking.positiveExpansion (base p) = (p.map cMap : QP) := by
  change N13TwoAdicInfinityCompatibility.powerMap (plus (base p)) = _
  rw [plus_base, beta_eq_coe]
  ext i
  simp [N13TwoAdicInfinityCompatibility.powerMap]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem generic_minus_base (p : R₂[X]) :
    N13InfinityChartMarking.negativeExpansion (base p) = (p.map cMap : QP) := by
  change N13TwoAdicInfinityCompatibility.powerMap (minus (base p)) = _
  rw [minus_base, beta_eq_coe]
  ext i
  simp [N13TwoAdicInfinityCompatibility.powerMap]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem generic_plus_v :
    N13InfinityChartMarking.positiveExpansion N13IntegralInfinityChart.vClass = r₀q := by
  change N13TwoAdicInfinityCompatibility.powerMap (plus N13IntegralInfinityChart.vClass) = _
  rw [plus_v]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem generic_minus_v :
    N13InfinityChartMarking.negativeExpansion N13IntegralInfinityChart.vClass = r₁q := by
  change N13TwoAdicInfinityCompatibility.powerMap (minus N13IntegralInfinityChart.vClass) = _
  rw [minus_v]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem trunc_error_dvd (f : QP) (n : ℕ) :
    (PowerSeries.X : QP) ^ n ∣ ((PowerSeries.trunc n f : Q₂[X]) : QP) - f := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro i hi
  simp [PowerSeries.coeff_trunc, hi]
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityBranchJetLift
noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Concrete simultaneous finite-jet lifting for the actual generic branch
maps. The one scalar c clears the two truncated interpolation polynomials. -/
theorem exists_scaled_branch_jet_lift (n : ℕ) (r s : QP) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ z : B,
      (PowerSeries.X : QP) ^ n ∣
        N13InfinityChartMarking.positiveExpansion z - PowerSeries.C (cMap c) * r ∧
      (PowerSeries.X : QP) ^ n ∣
        N13InfinityChartMarking.negativeExpansion z - PowerSeries.C (cMap c) * s := by
  let u := interpolationU r s
  let v := interpolationV r s
  obtain ⟨c, hc, p, q, hp, hq⟩ :=
    clear_two_polynomials (PowerSeries.trunc n u) (PowerSeries.trunc n v)
  let z : B := base p + base q * N13IntegralInfinityChart.vClass
  have hp' : (p.map cMap : QP) =
      (PowerSeries.trunc n u : QP) * PowerSeries.C (cMap c) := by
    rw [← hp]
    simp
  have hq' : (q.map cMap : QP) =
      (PowerSeries.trunc n v : QP) * PowerSeries.C (cMap c) := by
    rw [← hq]
    simp
  have hpz : N13InfinityChartMarking.positiveExpansion z =
      ((PowerSeries.trunc n u : QP) + (PowerSeries.trunc n v : QP) * r₀q) *
        PowerSeries.C (cMap c) := by
    dsimp only [z]
    rw [map_add, map_mul, generic_plus_base, generic_plus_base, generic_plus_v, hp', hq']
    ring
  have hmz : N13InfinityChartMarking.negativeExpansion z =
      ((PowerSeries.trunc n u : QP) + (PowerSeries.trunc n v : QP) * r₁q) *
        PowerSeries.C (cMap c) := by
    dsimp only [z]
    rw [map_add, map_mul, generic_minus_base, generic_minus_base, generic_minus_v, hp', hq']
    ring
  have hu := trunc_error_dvd u n
  have hv := trunc_error_dvd v n
  have hplus : u + v * r₀q = r := interpolation_plus r s
  have hminus : u + v * r₁q = s := interpolation_minus r s
  refine ⟨c, hc, z, ?_, ?_⟩
  · have h := (dvd_add hu (hv.trans (dvd_mul_right _ r₀q))).trans
      (dvd_mul_right _ (PowerSeries.C (cMap c)))
    convert h using 1
    rw [hpz, ← hplus]
    ring
  · have h := (dvd_add hu (hv.trans (dvd_mul_right _ r₁q))).trans
      (dvd_mul_right _ (PowerSeries.C (cMap c)))
    convert h using 1
    rw [hmz, ← hminus]
    ring
end
end MazurProof.N13InfinityBranchJetLift
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def toJets (n : ℕ) : B →+* JetPair n :=
  ((jetQuot n).comp N13InfinityChartMarking.positiveExpansion).prod
    ((jetQuot n).comp N13InfinityChartMarking.negativeExpansion)
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def scalar (n : ℕ) : R₂ →+* JetPair n := (toJets n).comp (algebraMap R₂ B)
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem positive_scalar (c : R₂) :
    N13InfinityChartMarking.positiveExpansion (algebraMap R₂ B c) =
      PowerSeries.C (cMap c) := by
  change N13InfinityChartMarking.positiveExpansion (base (Polynomial.C c)) = _
  rw [generic_plus_base]
  simp
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem negative_scalar (c : R₂) :
    N13InfinityChartMarking.negativeExpansion (algebraMap R₂ B c) =
      PowerSeries.C (cMap c) := by
  change N13InfinityChartMarking.negativeExpansion (base (Polynomial.C c)) = _
  rw [generic_minus_base]
  simp
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem toJets_eq_zero_iff (n : ℕ) (z : B) :
    toJets n z = 0 ↔ N13IntegralInfinityChart.tClass ^ n ∣ z := by
  rw [generic_branch_dvd_iff]
  constructor
  · intro h
    have hp : jetQuot n (N13InfinityChartMarking.positiveExpansion z) = 0 :=
      congrArg Prod.fst h
    have hm : jetQuot n (N13InfinityChartMarking.negativeExpansion z) = 0 :=
      congrArg Prod.snd h
    exact ⟨Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp),
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)⟩
  · rintro ⟨hp, hm⟩
    apply Prod.ext
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hp)
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hm)
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Every pair of finite generic jets is the jet of one integral chart
element up to a common nonzero Z2 scalar. -/
theorem exists_scaled_jet_pair (n : ℕ) (w : JetPair n) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ z : B, toJets n z = scalar n c * w := by
  rcases w with ⟨r, s⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨c, hc, z, hp, hm⟩ := exists_scaled_branch_jet_lift n r s
  refine ⟨c, hc, z, ?_⟩
  apply Prod.ext
  · change jetQuot n (N13InfinityChartMarking.positiveExpansion z) =
      jetQuot n (N13InfinityChartMarking.positiveExpansion (algebraMap R₂ B c)) * jetQuot n r
    rw [positive_scalar, ← map_mul]
    exact jet_eq_of_dvd_sub n _ _ hp
  · change jetQuot n (N13InfinityChartMarking.negativeExpansion z) =
      jetQuot n (N13InfinityChartMarking.negativeExpansion (algebraMap R₂ B c)) * jetQuot n s
    rw [negative_scalar, ← map_mul]
    exact jet_eq_of_dvd_sub n _ _ hm
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Jets that are represented by an element of J after one nonzero vertical
scalar. Jet lifting supplies closure under arbitrary coefficient pairs. -/
def scaledIdeal (n : ℕ) (J : Ideal B) : Ideal (JetPair n) where
  carrier := {w | ∃ c : R₂, c ≠ 0 ∧ ∃ z : B, z ∈ J ∧ toJets n z = scalar n c * w}
  zero_mem' := by
    refine ⟨1, one_ne_zero, 0, J.zero_mem, ?_⟩
    simp
  add_mem' := by
    intro u v hu hv
    obtain ⟨c, hc, x, hx, hxu⟩ := hu
    obtain ⟨d, hd, y, hy, hyv⟩ := hv
    refine ⟨c * d, mul_ne_zero hc hd,
      algebraMap R₂ B d * x + algebraMap R₂ B c * y,
      J.add_mem (J.mul_mem_left _ hx) (J.mul_mem_left _ hy), ?_⟩
    rw [map_add, map_mul, map_mul]
    change scalar n d * toJets n x + scalar n c * toJets n y = _
    rw [hxu, hyv, map_mul]
    ring
  smul_mem' := by
    intro u v hv
    obtain ⟨c, hc, x, hx, hxv⟩ := hv
    obtain ⟨d, hd, y, hyu⟩ := exists_scaled_jet_pair n u
    refine ⟨c * d, mul_ne_zero hc hd, y * x, J.mul_mem_left _ hx, ?_⟩
    change toJets n (y * x) = scalar n (c * d) * (u * v)
    rw [map_mul, hyu, hxv, map_mul]
    ring
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_toJets_le_scaledIdeal (n : ℕ) (J : Ideal B) :
    Ideal.map (toJets n) J ≤ scaledIdeal n J := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro z hz
  refine ⟨1, one_ne_zero, z, hz, ?_⟩
  simp
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
private theorem map_prod_eq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (I : Ideal R) :
    Ideal.map (f.prod g) I = Ideal.prod (Ideal.map f I) (Ideal.map g I) := by
  rw [Ideal.ideal_prod_eq (Ideal.map (f.prod g) I)]
  simp only [Ideal.map_map]
  rfl
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_toJets_eq_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (n : ℕ) : Ideal.map (toJets n) I = Ideal.map (toJets n) J := by
  unfold toJets
  rw [map_prod_eq, map_prod_eq]
  simp only [← Ideal.map_map]
  rw [hp, hm]
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13InfinityIdealApproximation
noncomputable section
open N13InfinityBranchJets N13InfinityBranchJetLift
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The actual two generic branch ideal equalities now produce an actual
ordinary-chart approximation to EVERY finite order. The nonzero vertical
scalar is explicit; it becomes invertible only on the generic fibre. -/
theorem scaled_approximations_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (x : B) (hx : x ∈ I) (n : ℕ) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ y : B,
      algebraMap R₂ B c * x - N13IntegralInfinityChart.tClass ^ n * y ∈ J := by
  have hj : toJets n x ∈ Ideal.map (toJets n) J := by
    rw [← map_toJets_eq_of_branch_eq I J hp hm n]
    exact Ideal.mem_map_of_mem (toJets n) hx
  obtain ⟨c, hc, z, hz, heq⟩ := map_toJets_le_scaledIdeal n J hj
  have hzero : toJets n (algebraMap R₂ B c * x - z) = 0 := by
    rw [map_sub, map_mul]
    change scalar n c * toJets n x - toJets n z = 0
    rw [heq, sub_self]
  obtain ⟨y, hy⟩ := (toJets_eq_zero_iff n _).mp hzero
  refine ⟨c, hc, y, ?_⟩
  have hsame : algebraMap R₂ B c * x - N13IntegralInfinityChart.tClass ^ n * y = z := by
    linear_combination hy
  rw [hsame]
  exact hz
end
end MazurProof.N13InfinityIdealApproximation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13LocalizationAdicPatch
noncomputable section
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
theorem eq_zero_of_nilpotent_and_adically_small
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (t : R) (x : M)
    (hnil : ∃ n : ℕ, t ^ n • x = 0)
    (hsmall : x ∈ ⨅ n : ℕ, Ideal.span ({t} : Set R) ^ n • (⊤ : Submodule R M)) :
    x = 0 := by
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨a, ha⟩ :=
    ((Ideal.span ({t} : Set R)).mem_iInf_smul_pow_eq_bot_iff x).mp hsmall
  have hat : t ∣ (a : R) := Ideal.mem_span_singleton.mp a.property
  obtain ⟨b, hab⟩ := hat
  have hpow : ∀ k : ℕ, (a : R) ^ k • x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_smul, ih, ha]
  calc
    x = (a : R) ^ n • x := (hpow n).symm
    _ = (t * b) ^ n • x := by rw [hab]
    _ = b ^ n • (t ^ n • x) := by rw [mul_pow, mul_comm, mul_smul]
    _ = 0 := by rw [hn, smul_zero]
end
end MazurProof.N13LocalizationAdicPatch
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13LocalizationAdicPatch
noncomputable section
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
/-- A finite module quotient cannot retain an element that both dies after
inverting t and is approximable by zero to every t-adic order. -/
theorem ideal_le_of_localization_le_of_approximations
    {T : Type*} [CommRing T] [Algebra R T]
    (t : R) [IsLocalization (Submonoid.powers t) T]
    (I J : Ideal R)
    (hAway : Ideal.map (algebraMap R T) I ≤ Ideal.map (algebraMap R T) J)
    (hApprox : ∀ x : R, x ∈ I → ∀ n : ℕ,
      ∃ y : R, x - t ^ n * y ∈ J) : I ≤ J := by
  intro x hx
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hnil : ∃ n : ℕ, t ^ n • q x = 0 := by
    have hm := hAway (Ideal.mem_map_of_mem (algebraMap R T) hx)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers t)] at hm
    obtain ⟨s, hs, hsx⟩ := hm
    obtain ⟨n, rfl⟩ := hs
    refine ⟨n, ?_⟩
    have hh : q (t ^ n * x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hsx
    simpa [q, Algebra.smul_def] using hh
  have hsmall : q x ∈ ⨅ n : ℕ,
      Ideal.span ({t} : Set R) ^ n • (⊤ : Submodule R (R ⧸ J)) := by
    refine (Submodule.mem_iInf _).mpr fun n => ?_
    obtain ⟨y, hy⟩ := hApprox x hx n
    have hh : q (x - t ^ n * y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have hq : q x = t ^ n • q y := by
      rw [map_sub, map_mul] at hh
      simpa [q, Algebra.smul_def] using sub_eq_zero.mp hh
    rw [hq]
    apply Submodule.smul_mem_smul
    · rw [Ideal.span_singleton_pow]
      exact Ideal.subset_span (Set.mem_singleton (t ^ n))
    · exact Submodule.mem_top
  have hxzero := eq_zero_of_nilpotent_and_adically_small t (q x) hnil hsmall
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
end
end MazurProof.N13LocalizationAdicPatch
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13LocalizationAdicPatch
noncomputable section
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
theorem ideal_eq_of_localization_eq_of_approximations
    {T : Type*} [CommRing T] [Algebra R T]
    (t : R) [IsLocalization (Submonoid.powers t) T]
    (I J : Ideal R)
    (hAway : Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J)
    (hIJ : ∀ x : R, x ∈ I → ∀ n : ℕ, ∃ y : R, x - t ^ n * y ∈ J)
    (hJI : ∀ x : R, x ∈ J → ∀ n : ℕ, ∃ y : R, x - t ^ n * y ∈ I) :
    I = J := by
  exact le_antisymm
    (ideal_le_of_localization_le_of_approximations t I J hAway.le hIJ)
    (ideal_le_of_localization_le_of_approximations t J I hAway.symm.le hJI)
end
end MazurProof.N13LocalizationAdicPatch
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GenericInfinityComparison
noncomputable section
open N13InfinityBranchJets N13InfinityIdealApproximation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem approximations_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (z : GenericInfinity) (hz : z ∈ Ideal.map (algebraMap B GenericInfinity) I) (n : ℕ) :
    ∃ w : GenericInfinity,
      z - genericT ^ n * w ∈ Ideal.map (algebraMap B GenericInfinity) J := by
  obtain ⟨⟨x, s⟩, hsz⟩ :=
    (IsLocalization.mem_map_algebraMap_iff verticalScalars GenericInfinity).mp hz
  obtain ⟨c, hc, y, hy⟩ := scaled_approximations_of_branch_eq I J hp hm x x.property n
  let sc : verticalScalars :=
    ⟨algebraMap R₂ B c, ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc, rfl⟩⟩
  have hunit : IsUnit
      (algebraMap B GenericInfinity (algebraMap R₂ B c) *
        algebraMap B GenericInfinity (s : B)) :=
    (IsLocalization.map_units GenericInfinity sc).mul
      (IsLocalization.map_units GenericInfinity s)
  let u : GenericInfinityˣ := hunit.unit
  have hu : (u : GenericInfinity) =
      algebraMap B GenericInfinity (algebraMap R₂ B c) *
        algebraMap B GenericInfinity (s : B) := hunit.unit_spec
  let Jg := Ideal.map (algebraMap B GenericInfinity) J
  have hscaled : (u : GenericInfinity) * z - genericT ^ n * algebraMap B GenericInfinity y ∈ Jg := by
    have hmap := Ideal.mem_map_of_mem (algebraMap B GenericInfinity) hy
    convert hmap using 1
    simp only [genericT, map_sub, map_mul, map_pow, hu]
    rw [← hsz]
    ring
  refine ⟨(↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y, ?_⟩
  have hmul := Jg.mul_mem_left (↑(u⁻¹) : GenericInfinity) hscaled
  have heq : (↑(u⁻¹) : GenericInfinity) *
      ((u : GenericInfinity) * z - genericT ^ n * algebraMap B GenericInfinity y) =
      z - genericT ^ n * ((↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y) := by
    calc
      _ = ((↑(u⁻¹) : GenericInfinity) * (u : GenericInfinity)) * z -
          genericT ^ n * ((↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  rwa [heq] at hmul
end
end MazurProof.N13GenericInfinityComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GenericInfinityComparison
noncomputable section
open N13InfinityBranchJets N13InfinityIdealApproximation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- For the actual generic ordinary infinity chart, equality on D(t) and
equality under BOTH actual generic Hensel-branch maps imply ideal equality.
The formerly missing approximation hypotheses are proved above. -/
theorem generic_ideal_eq_of_overlap_and_branches
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) I) =
        Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) J)) :
    Ideal.map (algebraMap B GenericInfinity) I = Ideal.map (algebraMap B GenericInfinity) J := by
  apply N13LocalizationAdicPatch.ideal_eq_of_localization_eq_of_approximations genericT _ _ hAway
  · intro z hz n
    exact approximations_of_branch_eq I J hp hm z hz n
  · intro z hz n
    exact approximations_of_branch_eq J I hp.symm hm.symm z hz n
end
end MazurProof.N13GenericInfinityComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GenericInfinityComparison
noncomputable section
open N13InfinityBranchJets N13InfinityIdealApproximation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Actual integral infinity-ideal equality follows as well when both
ideals are invertible and have nonzero reductions. Vertical denominators
are cancelled using the proved reduction-saturation theorem. -/
theorem integral_ideal_eq_of_overlap_and_branches
    (I J : Ideal B)
    (hI : IsUnit (I : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hJ : IsUnit (J : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hIr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥)
    (hJr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate J ≠ ⊥)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) I) =
        Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) J)) : I = J := by
  have hg := generic_ideal_eq_of_overlap_and_branches I J hp hm hAway
  have descend (U V : Ideal B)
      (hV : IsUnit (V : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
      (hVr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate V ≠ ⊥)
      (hmap : Ideal.map (algebraMap B GenericInfinity) U =
        Ideal.map (algebraMap B GenericInfinity) V) : U ≤ V := by
    intro x hx
    have hm := Ideal.mem_map_of_mem (algebraMap B GenericInfinity) hx
    rw [hmap, IsLocalization.algebraMap_mem_map_algebraMap_iff verticalScalars] at hm
    obtain ⟨q, hq, hqx⟩ := hm
    obtain ⟨r, hr, hqr⟩ := hq
    rw [← hqr] at hqx
    exact N13InvertibleReductionSaturation.twoAdic_scalar_saturated_of_reduction_ne_bot
      (K := N13IntegralInfinityPointSpread.FunctionField)
      N13IntegralInfinityReduction.reduceCoordinate
      N13InvertibleReductionSaturation.infinity_two_ne_zero
      N13IntegralInfinityReduction.ker_reduceCoordinate V hV hVr
      r (mem_nonZeroDivisors_iff_ne_zero.mp hr) x hqx
  exact le_antisymm (descend I J hJ hJr hg) (descend J I hI hIr hg.symm)
end
end MazurProof.N13GenericInfinityComparison
end
end

open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (I J : Ideal MazurProof.N13InfinityBranchJets.B)
    (hI : IsUnit (I : MazurProof.N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hJ : IsUnit (J : MazurProof.N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hIr : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥)
    (hJr : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate J ≠ ⊥)
    (hp : Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion I =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion I =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap MazurProof.N13GenericInfinityComparison.GenericInfinity MazurProof.N13GenericInfinityComparison.GenericOverlap)
          (Ideal.map (algebraMap MazurProof.N13InfinityBranchJets.B MazurProof.N13GenericInfinityComparison.GenericInfinity) I) =
        Ideal.map (algebraMap MazurProof.N13GenericInfinityComparison.GenericInfinity MazurProof.N13GenericInfinityComparison.GenericOverlap)
          (Ideal.map (algebraMap MazurProof.N13InfinityBranchJets.B MazurProof.N13GenericInfinityComparison.GenericInfinity) J)) : I = J := by
  exact MazurProof.N13GenericInfinityComparison.integral_ideal_eq_of_overlap_and_branches I J hI hJ hIr hJr hp hm hAway
