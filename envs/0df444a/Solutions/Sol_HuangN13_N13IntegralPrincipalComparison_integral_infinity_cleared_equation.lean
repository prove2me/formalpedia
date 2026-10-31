-- Prove2me | solution 1 for HuangN13.N13IntegralPrincipalComparison.integral_infinity_cleared_equation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:46:37.057965+00:00
-- url     : https://prove2.me/submissions/7d599fb5-9aeb-4a39-8aee-c12e14dca89e

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Theorems.Thm_HuangN13_N13GenericInfinityComparison_integral_ideal_eq_of_overlap_and_branches
import Theorems.Thm_HuangN13_N13IntegralPrincipalComparison_infinity_overlap_cleared_equation
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation

set_option autoImplicit false

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
  exact HuangN13.N13GenericInfinityComparison.integral_ideal_eq_of_overlap_and_branches I J hI hJ hIr hJr hp hm hAway
end
end MazurProof.N13GenericInfinityComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinity_overlap_cleared_equation
    (L M : Line) (a b : A) (c d : B) (hb : b ≠ 0)
    (haffine : Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    Ideal.map (algebraMap B O) (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map (algebraMap B O) (Ideal.span ({d} : Set B) * M.infinityIdeal) := by
  exact HuangN13.N13IntegralPrincipalComparison.infinity_overlap_cleared_equation L M a b c d hb haffine hcross
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem ordinaryToGenericOverlap_comp :
    ordinaryToGenericOverlap.comp (algebraMap B O) = infinityToGenericOverlap :=
  IsLocalization.Away.lift_comp N13IntegralInfinityChart.tClass t_unit
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem generic_away_equation_of_ordinary (I J : Ideal B)
    (h : Ideal.map (algebraMap B O) I = Ideal.map (algebraMap B O) J) :
    Ideal.map (algebraMap GenericInfinity GenericOverlap)
        (Ideal.map (algebraMap B GenericInfinity) I) =
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
        (Ideal.map (algebraMap B GenericInfinity) J) := by
  have hm := congrArg (Ideal.map ordinaryToGenericOverlap) h
  simpa only [Ideal.map_map, ordinaryToGenericOverlap_comp, infinityToGenericOverlap] using hm
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem principal_mul_infinity_isUnit (c : B) (hc : c ≠ 0) (L : Line) :
    IsUnit ((Ideal.span ({c} : Set B) * L.infinityIdeal : Ideal B) :
      N13IntegralInfinityPointSpread.InfinityFractionalIdeal) := by
  rw [FractionalIdeal.coeIdeal_mul]
  have hprincipal : IsUnit ((Ideal.span ({c} : Set B) : Ideal B) :
      N13IntegralInfinityPointSpread.InfinityFractionalIdeal) := by
    exact IsUnit.of_mul_eq_one _ (FractionalIdeal.coe_ideal_span_singleton_mul_inv
      N13IntegralInfinityPointSpread.FunctionField hc)
  exact hprincipal.mul L.infinity_isUnit
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem principal_mul_reduction_ne_bot
    (c : B) (hc : N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (I : Ideal B) (hI : Ideal.map N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate (Ideal.span ({c} : Set B) * I) ≠ ⊥ := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  intro h
  rcases Ideal.mul_eq_bot.mp h with hp | hI0
  · apply hc
    have hm := Ideal.mem_span_singleton_self (N13IntegralInfinityReduction.reduceCoordinate c)
    rwa [hp, Ideal.mem_bot] at hm
  · exact hI hI0
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralPrincipalComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13GenericInfinityComparison
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Once the affine equation and actual branch equations have been derived,
the whole integral infinity equation follows; no generic infinity ideal
equality or approximation predicate remains as an input. -/
theorem integral_infinity_cleared_equation
    (L M : Line) (a b : A) (c d : B) (hb : b ≠ 0)
    (hc : N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (hd : N13IntegralInfinityReduction.reduceCoordinate d ≠ 0)
    (hL : Ideal.map N13IntegralInfinityReduction.reduceCoordinate L.infinityIdeal ≠ ⊥)
    (hM : Ideal.map N13IntegralInfinityReduction.reduceCoordinate M.infinityIdeal ≠ ⊥)
    (haffine : Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c)
    (hplus : Ideal.map positiveExpansion (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map positiveExpansion (Ideal.span ({d} : Set B) * M.infinityIdeal))
    (hminus : Ideal.map negativeExpansion (Ideal.span ({c} : Set B) * L.infinityIdeal) =
      Ideal.map negativeExpansion (Ideal.span ({d} : Set B) * M.infinityIdeal)) :
    Ideal.span ({c} : Set B) * L.infinityIdeal = Ideal.span ({d} : Set B) * M.infinityIdeal := by
  exact integral_ideal_eq_of_overlap_and_branches _ _
    (principal_mul_infinity_isUnit c (fun h => hc (by simp [h])) L)
    (principal_mul_infinity_isUnit d (fun h => hd (by simp [h])) M)
    (principal_mul_reduction_ne_bot c hc _ hL)
    (principal_mul_reduction_ne_bot d hd _ hM) hplus hminus
    (generic_away_equation_of_ordinary _ _
      (infinity_overlap_cleared_equation L M a b c d hb haffine hcross))
end
end MazurProof.N13IntegralPrincipalComparison
end
end

open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (L M : MazurProof.N13TwoChartPicardRealization.Line) (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B) (hb : b ≠ 0)
    (hc : MazurProof.N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (hd : MazurProof.N13IntegralInfinityReduction.reduceCoordinate d ≠ 0)
    (hL : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate L.infinityIdeal ≠ ⊥)
    (hM : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate M.infinityIdeal ≠ ⊥)
    (haffine : Ideal.span ({a} : Set MazurProof.N13OverlapBranchCompatibility.A) * L.affineIdeal =
      Ideal.span ({b} : Set MazurProof.N13OverlapBranchCompatibility.A) * M.affineIdeal)
    (hcross : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c)
    (hplus : Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal) =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal))
    (hminus : Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal) =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal)) :
    Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal = Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal := by
  exact MazurProof.N13IntegralPrincipalComparison.integral_infinity_cleared_equation L M a b c d hb hc hd hL hM haffine hcross hplus hminus
