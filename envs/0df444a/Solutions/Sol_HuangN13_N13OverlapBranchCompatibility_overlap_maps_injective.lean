-- Prove2me | solution 1 for HuangN13.N13OverlapBranchCompatibility.overlap_maps_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:22:38.331259+00:00
-- url     : https://prove2.me/submissions/df0337ec-2aba-4670-be47-e0f7f92d88de

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_affineCurve_relation
import Theorems.Thm_MazurProof_N13FormalInfinityChart_infinityCurve_relation
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem sqrtReverseF_sq : sqrtReverseF K ^ 2 = reverseF K := by
  let h := reverseTail_hasSubst K
  change (PowerSeries.substAlgHom h
      (PowerSeries.binomialSeries K (1 / 2 : K))) ^ 2 = reverseF K
  rw [pow_two, ← map_mul, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := by norm_num
  rw [hhalf]
  have hone : PowerSeries.binomialSeries K (1 : K) =
      (1 + PowerSeries.X : K⟦X⟧) := by
    simpa using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)
  rw [hone]
  simp only [map_add, map_one,
    PowerSeries.substAlgHom_X]
  simp [reverseTail]
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K] in
theorem reverseF_coe :
    ((reverseF K : K⟦X⟧) : LaurentSeries K) =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  simp [reverseF, parameter, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_pow, map_ofNat]
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem wSeries_sq :
    wSeries K ^ 2 =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  rw [wSeries, ← PowerSeries.coe_pow, sqrtReverseF_sq, reverseF_coe]
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_scalar (c : K) :
    coordinateToLaurent K (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurent K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurent_xClass]
  simp
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurentMinus_scalar (c : K) :
    coordinateToLaurentMinus K
      (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurentMinus K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurentMinus_xClass]
  simp
end
end MazurProof.N13InfinityMinus
end
end

section
section
set_option autoImplicit false
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

section
section
set_option autoImplicit false
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

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem polyAtTInv_X :
    polyAtTInv X = tPow (-1) := by
  simp [polyAtTInv]
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The affine coefficient `x³+x+1` becomes
`t⁻³(1+t²+t³)`. -/
theorem polyAtTInv_hPoly :
    polyAtTInv
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      tPow (-3) *
        N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp only [N13GeneralizedMumfordIntegral.hPoly,
    map_add, map_pow, map_one, polyAtTInv_X]
  change
    tPow (-1) ^ 3 + tPow (-1) + 1 =
      tPow (-3) *
        (tPow 0 + tPow 2 + tPow 3)
  simp only [pow_succ, tPow_mul, mul_add, mul_one,
    tPow_zero]
  norm_num
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction of the actual integral affine coordinate ring to the
punctured formal infinity chart. -/
def affineToFormalCurve :
    IntegralAffineRing →+* FormalCurve :=
  AdjoinRoot.lift affineCoeffMap yImage affineCurve_relation
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToFormalCurve_xClass
    (p : R₂[X]) :
    affineToFormalCurve
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      algebraMap Laurent FormalCurve (polyAtTInv p) := by
  exact AdjoinRoot.lift_of affineCurve_relation
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToFormalCurve_yClass :
    affineToFormalCurve
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      yImage := by
  exact AdjoinRoot.lift_root affineCurve_relation
end
end MazurProof.N13FormalCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_vClass :
    infinityToFormalCurve vClass =
      N13FormalCurveOverlap.vClass := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13FormalInfinityChart
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
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem overlapEquiv_apply (z : AffineOverlap) :
    overlapEquiv z = affineOverlapToInfinityOverlap z :=
  rfl
end
end MazurProof.N13OrdinaryCurveOverlap
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
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZeroLaurent_of
    (f : Laurent) :
    evalBranchZeroLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZeroLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOneLaurent_of
    (f : Laurent) :
    evalBranchOneLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZeroLaurent_vClass :
    evalBranchZeroLaurent N13FormalCurveOverlap.vClass =
      branchZeroLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchZeroLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOneLaurent_vClass :
    evalBranchOneLaurent N13FormalCurveOverlap.vClass =
      branchOneLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extension commutes with the inclusion of power series into Laurent
series. -/
theorem laurentMap_includePower
    (f : IntegralPower) :
    laurentMap
        (N13FormalInfinityChart.includePowerRing f) =
      (HahnSeries.ofPowerSeries ℤ Q₂) (powerMap f) := by
  ext n
  rw [laurentMap_coeff]
  by_cases hn : n < 0
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_tPow
    (n : ℤ) :
    laurentMap (N13FormalCurveOverlap.tPow n) =
      tPowQ n := by
  ext m
  rw [laurentMap_coeff]
  by_cases hmn : m = n
  · subst m
    simp [N13FormalCurveOverlap.tPow, tPowQ]
  · simp [N13FormalCurveOverlap.tPow, tPowQ,
      hmn]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem laurentMap_cechTPow
    (n : ℤ) :
    laurentMap (N13FormalLineBundleCech.tPow n) =
      tPowQ n := by
  ext m
  rw [laurentMap_coeff]
  by_cases hmn : m = n
  · subst m
    simp [N13FormalLineBundleCech.tPow, tPowQ]
  · simp [N13FormalLineBundleCech.tPow, tPowQ,
      hmn]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem laurentMap_hInfinity :
    laurentMap
        (N13FormalLineBundleCech.hInfinity (R := R₂)) =
      hInfinityQ := by
  simp [N13FormalLineBundleCech.hInfinity,
    hInfinityQ]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem laurentMap_rhsInfinity :
    laurentMap
        (N13FormalLineBundleCech.rhsInfinity (R := R₂)) =
      rhsInfinityQ := by
  simp [N13FormalLineBundleCech.rhsInfinity,
    rhsInfinityQ]
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem powerMap_branchZero_constantCoeff :
    PowerSeries.constantCoeff
        (powerMap N13FormalInfinityBranches.branchZero) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    powerMap_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff]
  exact map_zero coeffMap
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
theorem wSeries_coeff_zero :
    (N13Infinity.wSeries Q₂).coeff (0 : ℤ) = 1 := by
  change
    (HahnSeries.ofPowerSeries ℤ Q₂
      (N13Infinity.sqrtReverseF Q₂)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem hInfinityQ_coeff_zero :
    hInfinityQ.coeff (0 : ℤ) = 1 := by
  simp [hInfinityQ, tPowQ]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
theorem wSeries_sq_eq_h_sq_add_four_rhs :
    N13Infinity.wSeries Q₂ ^ 2 =
      hInfinityQ ^ 2 + 4 * rhsInfinityQ := by
  rw [N13Infinity.wSeries_sq]
  have ht0 :
      tPowQ 0 = (1 : RationalLaurent) := rfl
  have ht1 :
      tPowQ 1 = N13Infinity.parameter Q₂ := rfl
  have ht2 :
      tPowQ 2 = N13Infinity.parameter Q₂ ^ 2 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  have ht3 :
      tPowQ 3 = N13Infinity.parameter Q₂ ^ 3 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  rw [hInfinityQ, rhsInfinityQ, ht0, ht1, ht2, ht3]
  ring
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
theorem tPowQ_three_mul_ySeries :
    tPowQ 3 * N13Infinity.ySeries Q₂ =
      N13Infinity.wSeries Q₂ := by
  have ht3 :
      tPowQ 3 = N13Infinity.parameter Q₂ ^ 3 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  rw [ht3, N13Infinity.ySeries, ← mul_assoc,
    ← mul_pow]
  simp [N13Infinity.parameter_ne_zero]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
theorem tPowQ_three_mul_ySeriesMinus :
    tPowQ 3 * N13InfinityMinus.ySeriesMinus Q₂ =
      -N13Infinity.wSeries Q₂ := by
  rw [N13InfinityMinus.ySeriesMinus_eq_neg]
  calc
    tPowQ 3 * -N13Infinity.ySeries Q₂ =
        -(tPowQ 3 * N13Infinity.ySeries Q₂) := by ring
    _ = -N13Infinity.wSeries Q₂ :=
      congrArg Neg.neg tPowQ_three_mul_ySeries
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
/-- The conjugate Hensel branch is the negative sextic Laurent branch after
the same coordinate change. -/
theorem rationalBranchOne_eq_negative :
    rationalBranchOne =
      algebraMap Q₂ RationalLaurent (1 / 2) *
        (tPowQ 3 *
            N13InfinityMinus.ySeriesMinus Q₂ -
          hInfinityQ) := by
  rw [tPowQ_three_mul_ySeriesMinus]
  have htwo :
      (2 : RationalLaurent) *
          algebraMap Q₂ RationalLaurent (1 / 2) = 1 := by
    rw [← map_ofNat
        (algebraMap Q₂ RationalLaurent) 2,
      ← map_mul]
    norm_num
  unfold rationalBranchOne rationalBranchZero
  linear_combination hInfinityQ * htwo
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem rationalBranchZero_coeff_zero :
    rationalBranchZero.coeff (0 : ℤ) = 0 := by
  unfold rationalBranchZero
  rw [HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]
  change
    ((HahnSeries.single 0 (1 / 2 : Q₂)) *
      (N13Infinity.wSeries Q₂ - hInfinityQ)).coeff
        (0 : ℤ) = 0
  rw [HahnSeries.coeff_single_zero_mul]
  simp [wSeries_coeff_zero, hInfinityQ_coeff_zero]
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
theorem rationalBranchZero_relation :
    rationalBranchZero ^ 2 +
        hInfinityQ * rationalBranchZero -
      rhsInfinityQ = 0 := by
  have hsq := wSeries_sq_eq_h_sq_add_four_rhs
  unfold rationalBranchZero
  have htwo :
      (2 : RationalLaurent) *
          algebraMap Q₂ RationalLaurent (1 / 2) = 1 := by
    rw [← map_ofNat
        (algebraMap Q₂ RationalLaurent) 2,
      ← map_mul]
    norm_num
  linear_combination
    algebraMap Q₂ RationalLaurent (1 / 2) ^ 2 * hsq +
      (-algebraMap Q₂ RationalLaurent (1 / 2) *
          N13Infinity.wSeries Q₂ * hInfinityQ +
        algebraMap Q₂ RationalLaurent (1 / 2) *
            hInfinityQ ^ 2 +
        (2 * algebraMap Q₂ RationalLaurent (1 / 2) + 1) *
            rhsInfinityQ) * htwo
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem mappedBranchZero_relation :
    laurentMap
          N13FormalOverlapSplit.branchZeroLaurent ^ 2 +
        hInfinityQ *
          laurentMap
            N13FormalOverlapSplit.branchZeroLaurent -
      rhsInfinityQ = 0 := by
  have h := congrArg laurentMap
    N13FormalOverlapSplit.branchZeroLaurent_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa using h
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem mappedBranchZero_coeff_zero :
    (laurentMap
      N13FormalOverlapSplit.branchZeroLaurent).coeff
        (0 : ℤ) = 0 := by
  rw [N13FormalOverlapSplit.branchZeroLaurent,
    laurentMap_includePower]
  rw [show (0 : ℤ) = (0 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
    powerMap_branchZero_constantCoeff
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
/-- A root of the rational formal equation with constant coefficient zero
is the distinguished positive branch. -/
theorem root_eq_rationalBranchZero
    (r : RationalLaurent)
    (hr :
      r ^ 2 + hInfinityQ * r - rhsInfinityQ = 0)
    (hr0 : r.coeff (0 : ℤ) = 0) :
    r = rationalBranchZero := by
  have hprod :
      (r - rationalBranchZero) *
          (r + rationalBranchZero + hInfinityQ) = 0 := by
    linear_combination hr - rationalBranchZero_relation
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hcoeff :=
      congrArg
        (fun z : RationalLaurent => z.coeff (0 : ℤ)) h
    simp [hr0, rationalBranchZero_coeff_zero,
      hInfinityQ_coeff_zero] at hcoeff
end
end MazurProof.N13TwoAdicInfinityCompatibility
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
@[simp] theorem laurentMap_branchZero :
    laurentMap N13FormalOverlapSplit.branchZeroLaurent =
      rationalBranchZero :=
  root_eq_rationalBranchZero _
    mappedBranchZero_relation mappedBranchZero_coeff_zero
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicInfinityCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_branchOne :
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
      rationalBranchOne := by
  calc
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
        laurentMap
          (N13FormalInfinityChart.includePowerRing
            (-N13FormalInfinityChart.hPower -
              N13FormalInfinityBranches.branchZero)) := by
          rw [N13FormalOverlapSplit.branchOneLaurent,
            N13FormalInfinityBranches.branchOne]
    _ =
        -laurentMap
            (N13FormalInfinityChart.includePowerRing
              N13FormalInfinityChart.hPower) -
          laurentMap
            N13FormalOverlapSplit.branchZeroLaurent := by
          simp [N13FormalOverlapSplit.branchZeroLaurent]
    _ = -hInfinityQ - rationalBranchZero := by
      rw [N13FormalInfinityChart.includePowerRing_hPower,
        laurentMap_hInfinity, laurentMap_branchZero]
    _ = rationalBranchOne := rfl
end
end MazurProof.N13TwoAdicInfinityCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem toFormalInfinity_of
    (p : N13IntegralInfinityChart.Base) :
    N13IntegralInfinityChart.toFormalInfinity
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) =
      algebraMap
        N13IntegralInfinityChart.Power
        FormalInfinityCurve
        (N13IntegralInfinityChart.baseToPower p) := by
  exact
    AdjoinRoot.lift_of
      N13IntegralInfinityChart.formal_v_relation
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_coefficient
    (r : R₂) :
    infinityToFormalCurve
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly
          (Polynomial.C r)) =
      algebraMap Laurent FormalCurve
        (algebraMap R₂ Laurent r) := by
  rw [infinityToFormalCurve, RingHom.comp_apply,
    toFormalInfinity_of,
    N13FormalInfinityChart.infinityToFormalCurve_of]
  simp [N13IntegralInfinityChart.baseToPower,
    N13FormalInfinityChart.includePowerRing]
  congr 1
  rw [HahnSeries.algebraMap_apply',
    ← PowerSeries.C_eq_algebraMap,
    HahnSeries.ofPowerSeries_C]
  rfl
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_vClass :
    infinityToFormalCurve N13IntegralInfinityChart.vClass =
      N13FormalCurveOverlap.vClass := by
  simp [infinityToFormalCurve]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem infinity_tClass_isUnit :
    IsUnit
      (infinityToFormalCurve
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToFormalCurve_tClass]
  exact
    (tPowUnit 1).isUnit.map
      (algebraMap Laurent FormalCurve)
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The completion map restricts to the prescribed infinity-chart map. -/
@[simp] theorem ordinaryToFormalCurve_comp_infinity :
    ordinaryToFormalCurve.comp
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap) =
      infinityToFormalCurve := by
  exact
    IsLocalization.Away.lift_comp
      N13IntegralInfinityChart.tClass
      infinity_tClass_isUnit
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem ordinaryToFormalCurve_algebraMap
    (z : OrdinaryInfinityCurve) :
    ordinaryToFormalCurve
        (algebraMap OrdinaryInfinityCurve OrdinaryOverlap z) =
      infinityToFormalCurve z :=
  DFunLike.congr_fun ordinaryToFormalCurve_comp_infinity z
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem ordinaryToFormalCurve_tOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.tOverlap =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow 1) := by
  rw [N13OrdinaryCurveOverlap.tOverlap,
    ordinaryToFormalCurve_algebraMap,
    infinityToFormalCurve_tClass]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem ordinaryToFormalCurve_vOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.vOverlap =
      N13FormalCurveOverlap.vClass := by
  rw [N13OrdinaryCurveOverlap.vOverlap,
    ordinaryToFormalCurve_algebraMap,
    infinityToFormalCurve_vClass]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The distinguished ordinary inverse maps to the Laurent monomial
`t⁻¹`. -/
@[simp] theorem ordinaryToFormalCurve_xOverlap :
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow (-1)) := by
  have hmul :
      infinityToFormalCurve N13IntegralInfinityChart.tClass *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap = 1 := by
    calc
      infinityToFormalCurve N13IntegralInfinityChart.tClass *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap =
          ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.tOverlap *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap := by
                rw [ordinaryToFormalCurve_tOverlap,
                  infinityToFormalCurve_tClass]
      _ =
          ordinaryToFormalCurve
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by
                rw [map_mul]
      _ = 1 := by
        rw [N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap,
          map_one]
  calc
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
        1 *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap := by simp
    _ =
        (algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow (-1)) *
          algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow 1)) *
          ordinaryToFormalCurve
            N13OrdinaryCurveOverlap.xOverlap := by
              rw [← map_mul,
                N13FormalCurveOverlap.tPow_mul]
              norm_num
    _ =
        algebraMap Laurent FormalCurve
            (N13FormalCurveOverlap.tPow (-1)) *
          (infinityToFormalCurve
              N13IntegralInfinityChart.tClass *
            ordinaryToFormalCurve
              N13OrdinaryCurveOverlap.xOverlap) := by
                rw [infinityToFormalCurve_tClass, mul_assoc]
    _ =
        algebraMap Laurent FormalCurve
          (N13FormalCurveOverlap.tPow (-1)) := by
            rw [hmul, mul_one]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The formal affine map on the coefficient presentation. -/
@[simp] theorem affineToFormalCurve_of (p : Polynomial R₂) :
    N13FormalCurveOverlap.affineToFormalCurve
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)) p) =
      N13FormalCurveOverlap.affineCoeffMap p := by
  exact
    AdjoinRoot.lift_of
      N13FormalCurveOverlap.affineCurve_relation
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Completion agrees on constants of the affine presentation. -/
theorem ordinaryToFormalCurve_affine_coefficient
    (r : R₂) :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          (AdjoinRoot.of
            (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
            (Polynomial.C r))) =
      N13FormalCurveOverlap.affineToFormalCurve
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
          (Polynomial.C r)) := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_of,
    affineToFormalCurve_of]
  simp [N13OrdinaryCurveOverlap.affineCoeffMap,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap,
    N13FormalCurveOverlap.affineCoeffMap,
    N13FormalCurveOverlap.polyAtTInv]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Completion agrees on the affine coordinate `x`. -/
theorem ordinaryToFormalCurve_affine_x :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          N13OrdinaryCurveOverlap.xClass) =
      N13FormalCurveOverlap.affineToFormalCurve
        N13OrdinaryCurveOverlap.xClass := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClass]
  change
    ordinaryToFormalCurve N13OrdinaryCurveOverlap.xOverlap =
      N13FormalCurveOverlap.affineToFormalCurve
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) Polynomial.X)
  rw [ordinaryToFormalCurve_xOverlap,
    N13FormalCurveOverlap.affineToFormalCurve_xClass]
  simp [N13FormalCurveOverlap.polyAtTInv]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Completion agrees on the affine coordinate `y`. -/
theorem ordinaryToFormalCurve_affine_y :
    ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap
          N13OrdinaryCurveOverlap.yClass) =
      N13FormalCurveOverlap.affineToFormalCurve
        N13OrdinaryCurveOverlap.yClass := by
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_yClass]
  change
      ordinaryToFormalCurve
          N13OrdinaryCurveOverlap.affineYImage =
        N13FormalCurveOverlap.affineToFormalCurve
          (N13GeneralizedMumfordIntegral.yClass (R := R₂))
  rw [N13FormalCurveOverlap.affineToFormalCurve_yClass]
  simp only [N13OrdinaryCurveOverlap.affineYImage,
    map_mul, map_pow, ordinaryToFormalCurve_xOverlap,
    ordinaryToFormalCurve_vOverlap,
    N13FormalCurveOverlap.yImage]
  rw [← map_pow]
  congr 1
  simp [N13FormalCurveOverlap.tPow, HahnSeries.single_pow]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Completion is compatible with the ordinary affine restriction. -/
theorem ordinaryToFormalCurve_comp_affine :
    ordinaryToFormalCurve.comp
        N13OrdinaryCurveOverlap.affineToInfinityOverlap =
      N13FormalCurveOverlap.affineToFormalCurve := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · exact ordinaryToFormalCurve_affine_coefficient
    · exact ordinaryToFormalCurve_affine_x
  · exact ordinaryToFormalCurve_affine_y
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_tPow
    (n : ℤ) :
    laurentMap (N13FormalCurveOverlap.tPow n) =
      tPowQ n :=
  N13TwoAdicInfinityCompatibility.laurentMap_tPow n
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_branchZero :
    laurentMap N13FormalOverlapSplit.branchZeroLaurent =
      N13TwoAdicInfinityCompatibility.rationalBranchZero :=
  N13TwoAdicInfinityCompatibility.laurentMap_branchZero
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_branchOne :
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
      N13TwoAdicInfinityCompatibility.rationalBranchOne :=
  N13TwoAdicInfinityCompatibility.laurentMap_branchOne
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem laurentMap_algebraMap
    (a : R₂) :
    laurentMap (algebraMap R₂ IntegralLaurent a) =
      algebraMap Q₂ RationalLaurent (coeffMap a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  change
    ((HahnSeries.single (0 : ℤ) a).map coeffMap :
        RationalLaurent) =
      HahnSeries.single (0 : ℤ) (coeffMap a)
  exact HahnSeries.map_single coeffMap.toZeroHom
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tPowQ_neg_one :
    tPowQ (-1) =
      (N13Infinity.parameter Q₂)⁻¹ := by
  simp [tPowQ, N13TwoAdicInfinityCompatibility.tPowQ,
    N13Infinity.parameter, HahnSeries.inv_single]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tPowQ_neg_three :
    tPowQ (-3) =
      (N13Infinity.parameter Q₂)⁻¹ ^ 3 := by
  simp [tPowQ, N13TwoAdicInfinityCompatibility.tPowQ,
    N13Infinity.parameter, HahnSeries.inv_single,
    HahnSeries.single_pow]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coefficient extension commutes with evaluating an integral polynomial
at `t⁻¹`. -/
theorem laurentMap_polyAtTInv
    (p : R₂[X]) :
    laurentMap
        (N13FormalCurveOverlap.polyAtTInv p) =
      (p.map coeffMap).eval₂
        (algebraMap Q₂ RationalLaurent)
        ((N13Infinity.parameter Q₂)⁻¹) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | monomial n a =>
      change
        laurentMap
            ((monomial n a).eval₂
              (algebraMap R₂ IntegralLaurent)
              (N13FormalCurveOverlap.tPow (-1))) =
          ((monomial n a).map coeffMap).eval₂
            (algebraMap Q₂ RationalLaurent)
            ((N13Infinity.parameter Q₂)⁻¹)
      rw [Polynomial.eval₂_monomial,
        Polynomial.map_monomial,
        Polynomial.eval₂_monomial]
      rw [map_mul, map_pow, laurentMap_algebraMap,
        laurentMap_tPow,
        tPowQ_neg_one]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem rational_hPoly_at_infinity :
    (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)).eval₂
        (algebraMap Q₂ RationalLaurent)
        ((N13Infinity.parameter Q₂)⁻¹) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.hInfinityQ := by
  have h := congrArg laurentMap
    N13FormalCurveOverlap.polyAtTInv_hPoly
  rw [laurentMap_polyAtTInv] at h
  simp only [map_mul] at h
  change
    (N13TwoAdicCoordinateBaseChange.mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂))).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹) =
      laurentMap (N13FormalCurveOverlap.tPow (-3)) *
        laurentMap
          (N13FormalLineBundleCech.hInfinity (R := R₂)) at h
  rw [N13TwoAdicCoordinateBaseChange.mapPoly_hPoly] at h
  simpa [laurentMap, tPowQ] using h
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem ySeries_eq_tPowQ_negThree_mul_wSeries :
    N13Infinity.ySeries Q₂ =
      tPowQ (-3) * N13Infinity.wSeries Q₂ := by
  rw [N13Infinity.ySeries, tPowQ_neg_three]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem ySeriesMinus_eq_tPowQ_negThree_mul_neg_wSeries :
    N13InfinityMinus.ySeriesMinus Q₂ =
      tPowQ (-3) * -N13Infinity.wSeries Q₂ := by
  rw [N13InfinityMinus.ySeriesMinus_eq_neg,
    ySeries_eq_tPowQ_negThree_mul_wSeries]
  ring
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem rationalBranchOne_eq_neg_wSeries :
    N13TwoAdicInfinityCompatibility.rationalBranchOne =
      algebraMap Q₂ RationalLaurent (1 / 2) *
        (-N13Infinity.wSeries Q₂ -
          N13TwoAdicInfinityCompatibility.hInfinityQ) := by
  rw [
    N13TwoAdicInfinityCompatibility.rationalBranchOne_eq_negative,
    N13TwoAdicInfinityCompatibility.tPowQ_three_mul_ySeriesMinus]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Restriction of the good `y` coordinate to the positive rational branch. -/
theorem coordinateToLaurent_goodYInSextic :
    N13Infinity.coordinateToLaurent Q₂
        (N13GoodSexticCoordinateEquiv.goodYInSextic
          (K := Q₂)) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.rationalBranchZero := by
  simp only [N13GoodSexticCoordinateEquiv.goodYInSextic,
    Algebra.smul_def, map_mul, map_sub,
    N13GoodSexticCoordinateEquiv.sexticXHom_apply,
    N13Infinity.coordinateToLaurent_scalar,
    N13BranchNorm.coordinateToLaurent_yClass,
    N13Infinity.coordinateToLaurent_xClass]
  rw [rational_hPoly_at_infinity,
    ySeries_eq_tPowQ_negThree_mul_wSeries]
  unfold N13TwoAdicInfinityCompatibility.rationalBranchZero
  ring
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Restriction of the good `y` coordinate to the negative rational branch. -/
theorem coordinateToLaurentMinus_goodYInSextic :
    N13InfinityMinus.coordinateToLaurentMinus Q₂
        (N13GoodSexticCoordinateEquiv.goodYInSextic
          (K := Q₂)) =
      tPowQ (-3) *
        N13TwoAdicInfinityCompatibility.rationalBranchOne := by
  simp only [N13GoodSexticCoordinateEquiv.goodYInSextic,
    Algebra.smul_def, map_mul, map_sub,
    N13GoodSexticCoordinateEquiv.sexticXHom_apply,
    N13InfinityMinus.coordinateToLaurentMinus_scalar,
    N13InfinityMinus.coordinateToLaurentMinus_yClass,
    N13InfinityMinus.coordinateToLaurentMinus_xClass]
  rw [rational_hPoly_at_infinity,
    ySeriesMinus_eq_tPowQ_negThree_mul_neg_wSeries,
    rationalBranchOne_eq_neg_wSeries]
  ring
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Restrict to the integral formal overlap and evaluate on its two Hensel
branches. -/
def integralFormalBranches :
    IntegralRing →+* IntegralBranchPair :=
  N13FormalOverlapSplit.formalBranchEval.comp
    N13FormalCurveOverlap.affineToFormalCurve
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The integral-formal route around the restriction square. -/
def integralViaFormalBranches :
    IntegralRing →+* RationalBranchPair :=
  laurentPairMap.comp integralFormalBranches
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The rational-sextic route around the restriction square. -/
def integralViaRationalBranches :
    IntegralRing →+* RationalBranchPair :=
  (N13TwoInfinityRestriction.coordinateToBranches Q₂).comp
    N13TwoAdicCoordinateBaseChange.integralToSextic
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralFormalBranches_xClass
    (p : R₂[X]) :
    integralFormalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      (N13FormalCurveOverlap.polyAtTInv p,
        N13FormalCurveOverlap.polyAtTInv p) := by
  simp [integralFormalBranches,
    N13FormalOverlapSplit.formalBranchEval]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralFormalBranches_yClass :
    integralFormalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (N13FormalCurveOverlap.tPow (-3) *
          N13FormalOverlapSplit.branchZeroLaurent,
        N13FormalCurveOverlap.tPow (-3) *
          N13FormalOverlapSplit.branchOneLaurent) := by
  simp [integralFormalBranches,
    N13FormalOverlapSplit.formalBranchEval,
    N13FormalCurveOverlap.yImage]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralViaFormalBranches_xClass
    (p : R₂[X]) :
    integralViaFormalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      ((p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹),
        (p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹)) := by
  simp [integralViaFormalBranches,
    laurentMap_polyAtTInv]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralViaFormalBranches_yClass :
    integralViaFormalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchZero,
        tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchOne) := by
  simp [integralViaFormalBranches, map_mul,
    laurentMap_branchZero, laurentMap_branchOne]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralViaRationalBranches_xClass
    (p : R₂[X]) :
    integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.xClass
          (R := R₂) p) =
      ((p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹),
        (p.map coeffMap).eval₂
          (algebraMap Q₂ RationalLaurent)
          ((N13Infinity.parameter Q₂)⁻¹)) := by
  simp [integralViaRationalBranches,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    N13TwoInfinityRestriction.coordinateToBranches,
    N13TwoAdicCoordinateBaseChange.mapPoly, coeffMap]
  rfl
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem integralViaRationalBranches_yClass :
    integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.yClass
          (R := R₂)) =
      (tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchZero,
        tPowQ (-3) *
          N13TwoAdicInfinityCompatibility.rationalBranchOne) := by
  simp [integralViaRationalBranches,
    N13TwoAdicCoordinateBaseChange.integralToSextic,
    N13TwoInfinityRestriction.coordinateToBranches,
    coordinateToLaurent_goodYInSextic,
    coordinateToLaurentMinus_goodYInSextic]
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13TwoAdicAffineRestrictionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Pointwise commutativity of the affine restriction/base-change square. -/
theorem affineRestriction_commutes
    (z : IntegralRing) :
    integralViaFormalBranches z =
      integralViaRationalBranches z := by
  calc
    integralViaFormalBranches z =
        integralViaFormalBranches
          (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) := by
          exact congrArg integralViaFormalBranches
            (N13GeneralizedMumfordIntegral.recompose z).symm
    _ =
        integralViaRationalBranches
          (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp
    _ = integralViaRationalBranches z := by
      exact congrArg integralViaRationalBranches
        (N13GeneralizedMumfordIntegral.recompose z)
end
end MazurProof.N13TwoAdicAffineRestrictionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem overlapBranches_affine (a : A) :
    overlapBranches (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13TwoInfinityRestriction.coordinateToBranches Q₂
        (N13IntegralFractionalHull.integralToRational a) := by
  have h := DFunLike.congr_fun
    N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve_comp_affine a
  change N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
    (N13FormalOverlapSplit.formalBranchEval
      (N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a))) = _
  have h' : N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve
      (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13FormalCurveOverlap.affineToFormalCurve a := h
  rw [h']
  exact N13TwoAdicAffineRestrictionCompatibility.affineRestriction_commutes a
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem positiveOverlap_affine (a : A) :
    positiveOverlap (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13Infinity.coordinateToLaurent Q₂
        (N13IntegralFractionalHull.integralToRational a) :=
  congrArg Prod.fst (overlapBranches_affine a)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem negativeOverlap_affine (a : A) :
    negativeOverlap (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13InfinityMinus.coordinateToLaurentMinus Q₂
        (N13IntegralFractionalHull.integralToRational a) :=
  congrArg Prod.snd (overlapBranches_affine a)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
private theorem localization_hom_injective
    {R S T : Type*} [CommRing R] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (f : S →+* T) (hf : Function.Injective (f.comp (algebraMap R S))) :
    Function.Injective f := by
  have hzero (z : S) (hz : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M z
    have hfa : f (algebraMap R S a) = 0 := by
      rw [← ha, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hf (by simpa using hfa)
    rw [ha0, map_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right (IsLocalization.map_units S s).ne_zero
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by simp [map_sub, hxy]))
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem positiveOverlap_injective : Function.Injective positiveOverlap := by
  have h : Function.Injective
      (positiveOverlap.comp N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
    have hi := (N13Infinity.coordinateToLaurent_injective Q₂).comp
      N13IntegralFractionalHull.integralToRational_injective
    intro a b hab
    apply hi
    change positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO a)) =
      positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO b)) at hab
    simp only [N13OrdinaryCurveOverlap.overlapEquiv_apply,
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      positiveOverlap_affine] at hab
    exact hab
  intro x y hxy
  apply N13OrdinaryCurveOverlap.overlapEquiv.symm.injective
  apply h
  change positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm x)) =
    positiveOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm y))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hxy
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem negativeOverlap_injective : Function.Injective negativeOverlap := by
  have h : Function.Injective
      (negativeOverlap.comp N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
    have hi := (N13InfinityMinus.coordinateToLaurentMinus_injective Q₂).comp
      N13IntegralFractionalHull.integralToRational_injective
    intro a b hab
    apply hi
    change negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO a)) =
      negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv (algebraMap A AO b)) at hab
    simp only [N13OrdinaryCurveOverlap.overlapEquiv_apply,
      N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      negativeOverlap_affine] at hab
    exact hab
  intro x y hxy
  apply N13OrdinaryCurveOverlap.overlapEquiv.symm.injective
  apply h
  change negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm x)) =
    negativeOverlap (N13OrdinaryCurveOverlap.overlapEquiv
      (N13OrdinaryCurveOverlap.overlapEquiv.symm y))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hxy
end
end MazurProof.N13OverlapBranchCompatibility
end
end

attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution : Function.Injective MazurProof.N13OverlapBranchCompatibility.positiveOverlap ∧
    Function.Injective MazurProof.N13OverlapBranchCompatibility.negativeOverlap := by
  exact ⟨MazurProof.N13OverlapBranchCompatibility.positiveOverlap_injective, MazurProof.N13OverlapBranchCompatibility.negativeOverlap_injective⟩
