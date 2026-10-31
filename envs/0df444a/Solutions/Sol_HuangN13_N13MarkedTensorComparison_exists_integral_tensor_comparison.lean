-- Prove2me | solution 1 for HuangN13.N13MarkedTensorComparison.exists_integral_tensor_comparison
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:14:16.554976+00:00
-- url     : https://prove2.me/submissions/6ce4e644-ec28-44a8-b4d7-d8b5af934c1d

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Theorems.Thm_HuangN13_N13IntegralPrincipalComparison_integral_infinity_cleared_equation
import Theorems.Thm_HuangN13_N13PrimitiveAffineComparison_integral_cleared_equation
import Theorems.Thm_HuangN13_N13PrincipalBranchIdeals_tensor_branch_ideal_equations
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13QuadraticTwoChartSpreadSaturation_mul_scalar_saturated_of_left_isUnit
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityCoeffMap_hPoly
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_map_infinityPointIdeal
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_overlap_unitPointIdeal

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

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
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduce_coeff0 (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeff0 z) := by
  calc
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeff0
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeff0_xClass,
        N13GoodCoordinateRingTwo.coeff0_xClass_mul_yClass,
        add_zero]
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduce_coeffY (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeffY z) := by
  calc
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeffY
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeffY_xClass,
        N13GoodCoordinateRingTwo.coeffY_xClass_mul_yClass,
        zero_add]
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
private theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : R₂[X]) (hp : reducePoly p = 0) :
    ∃ q : R₂[X], p = C (2 : R₂) * q := by
  have hmem :
      p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
/-- Reduction has exactly the vertical principal ideal `(2)` as kernel.
The proof combines the rank-two normal form with the polynomial-map kernel
theorem and the standard description of the maximal ideal of `ℤ₂`. -/
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
        reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) = 0 := by
      rw [← reduce_coeff0 z, hz0]
      simp
    have hY :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) = 0 := by
      rw [← reduce_coeffY z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hY
    rw [Ideal.mem_span_singleton]
    refine ⟨
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass,
      ?_⟩
    rw [← N13GeneralizedMumfordIntegral.recompose z, hp, hq]
    calc
      N13GeneralizedMumfordIntegral.xClass (C 2 * p) +
          N13GeneralizedMumfordIntegral.xClass (C 2 * q) *
            N13GeneralizedMumfordIntegral.yClass =
        N13GeneralizedMumfordIntegral.xClass (C 2) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp only [mul_add,
            N13GeneralizedMumfordIntegral.xClass_mul]
          ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate
      (N13GeneralizedMumfordIntegral.xClass (C (2 : R₂))) = 0
    rw [reduce_xClass]
    simp [reducePoly]
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tensor_affineIdeal (L M : TwoChartLine) :
    (tensor L M).affineIdeal =
      L.affineIdeal * M.affineIdeal :=
  rfl
end
end MazurProof.N13TwoChartLineTensor
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
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem tensor_infinityIdeal (L M : TwoChartLine) :
    (tensor L M).infinityIdeal =
      L.infinityIdeal * M.infinityIdeal :=
  rfl
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
theorem infinityCurve_relation :
    N13SpecialInfinityChart.curvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13SpecialInfinityChart.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hPoly,
    infinityCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- Restriction of the infinity coordinate ring to the special affine
principal open. -/
def infinityToAffineOverlap :
    CoordinateRing →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13SpecialInfinityChart.curvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13SpecialInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13SpecialInfinityChart.tClass, infinityCoeffMap]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13SpecialInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13SpecialInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13SpecialInfinityChart.tClass
    infinity_tClass_mapsToUnit
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : CoordinateRing) :
    infinityOverlapToAffineOverlap
        (algebraMap CoordinateRing InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13SpecialInfinityChart.tClass
      infinity_tClass_mapsToUnit z
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
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
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
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
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The reverse special overlap map is a left inverse of the forward map. -/
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
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
/-- The forward special overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13SpecialInfinityChart.tClass)
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
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- The special principal opens of the affine and infinity charts agree. -/
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
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
@[simp] theorem overlapEquiv_apply (z : AffineOverlap) :
    overlapEquiv z = affineOverlapToInfinityOverlap z :=
  rfl
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralFunctionFieldFractionRing MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coercing the generic ideal unit to a fractional ideal recovers the
literal extension of the line's affine ideal.

This bridge is independent of the geometric origin of the proper line and is
therefore shared by point and quadratic Picard realizations. -/
@[simp] theorem coe_genericIdealUnit
    (L : Line) :
    (genericIdealUnit L :
        N13IntegralFractionalHull.RationalFractionalIdeal) =
      (Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal :
        N13IntegralFractionalHull.RationalFractionalIdeal) := by
  change
    N13IntegralFractionalHull.extendFractional
        (L.affine_isUnit.unit :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      _
  rw [L.affine_isUnit.unit_spec,
    N13IntegralFractionalHull.extendFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
/-- Tensoring two vertically saturated two-chart lines preserves vertical
saturation on the affine chart.  Invertibility of the first affine ideal is
the essential hypothesis supplied by the line structure. -/
theorem affineVerticallySaturated_tensor
    (L M : N13TwoChartPicardRealization.Line)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L)
    (hM : N13TwoChartPicardRealization.AffineVerticallySaturated M) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor L M) := by
  change
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ L.affineIdeal * M.affineIdeal →
        a ∈ L.affineIdeal * M.affineIdeal
  exact
    mul_scalar_saturated_of_left_isUnit
      L.affineIdeal M.affineIdeal L.affine_isUnit hL hM
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
private instance instIsDomainOs : IsDomain Os :=
  N13SpecialCurveOverlap.overlapEquiv.symm.toMulEquiv.isDomain AOs
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
theorem special_affineToInfinityOverlap_injective :
    Function.Injective N13SpecialCurveOverlap.affineToInfinityOverlap := by
  intro a b hab
  apply IsLocalization.injective AOs
    (powers_le_nonZeroDivisors_of_noZeroDivisors special_x_ne_zero)
  apply N13SpecialCurveOverlap.overlapEquiv.injective
  simpa only [N13SpecialCurveOverlap.overlapEquiv_apply,
    N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap] using hab
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem reduce_affine (a : A) :
    N13OverlapReductionCompatibility.reduceInfinityOverlap
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
      N13SpecialCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
  DFunLike.congr_fun
    N13TwoChartSpecialRestriction.reduceInfinityOverlap_comp_affineToInfinityOverlap a
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem reduce_infinity (b : B) :
    N13OverlapReductionCompatibility.reduceInfinityOverlap (algebraMap B O b) =
      algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate b) :=
  DFunLike.congr_fun
    N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap b
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem reduced_overlap_t_isUnit :
    IsUnit (N13OverlapReductionCompatibility.reduceInfinityOverlap
      (algebraMap B O N13IntegralInfinityChart.tClass)) :=
  (IsLocalization.Away.algebraMap_isUnit N13IntegralInfinityChart.tClass :
    IsUnit (algebraMap B O N13IntegralInfinityChart.tClass)).map
      N13OverlapReductionCompatibility.reduceInfinityOverlap
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem reduced_t_ne_zero :
    N13IntegralInfinityReduction.reduceCoordinate N13IntegralInfinityChart.tClass ≠ 0 := by
  intro ht
  apply reduced_overlap_t_isUnit.ne_zero
  rw [reduce_infinity, ht, map_zero]
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Clear only a power of t in a single affine function. Nonzero reduction
survives because the reduced affine restriction is injective and t is a unit
on the reduced overlap. -/
theorem exists_infinity_numerator
    (a : A) (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0) :
    ∃ n : ℕ, ∃ c : B,
      N13IntegralInfinityReduction.reduceCoordinate c ≠ 0 ∧
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ n =
        algebraMap B O c := by
  obtain ⟨⟨c, s⟩, hc⟩ := IsLocalization.surj
    (Submonoid.powers N13IntegralInfinityChart.tClass)
    (N13OrdinaryCurveOverlap.affineToInfinityOverlap a)
  obtain ⟨n, hn⟩ := s.property
  have hs : algebraMap B O (s : B) =
      (algebraMap B O N13IntegralInfinityChart.tClass) ^ n := by
    rw [← hn, map_pow]
  have hc' : N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
      (algebraMap B O N13IntegralInfinityChart.tClass) ^ n = algebraMap B O c := by
    simpa only [hs] using hc
  refine ⟨n, c, ?_, hc'⟩
  intro hc0
  have haO : N13OverlapReductionCompatibility.reduceInfinityOverlap
      (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) ≠ 0 := by
    rw [reduce_affine, ← map_zero N13SpecialCurveOverlap.affineToInfinityOverlap]
    exact special_affineToInfinityOverlap_injective.ne ha
  have htO := reduced_overlap_t_isUnit.ne_zero
  have hm := congrArg N13OverlapReductionCompatibility.reduceInfinityOverlap hc'
  have hreduce_c : N13OverlapReductionCompatibility.reduceInfinityOverlap ((algebraMap B O) c) =
      algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate c) := by
    simp [N13OverlapReductionCompatibility.reduceInfinityOverlap_algebraMap]
    rfl
  simp only [map_mul, map_pow] at hm
  rw [hreduce_c, hc0, map_zero] at hm
  exact (mul_ne_zero haO (pow_ne_zero n htO)) hm
end
end MazurProof.N13PrimitiveChartTransport
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveChartTransport
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Every affine primitive fraction admits a primitive infinity-chart
presentation of exactly the same fraction on the ordinary overlap. -/
theorem exists_common_primitive_presentation
    (a b : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0) :
    ∃ c d : B,
      N13IntegralInfinityReduction.reduceCoordinate c ≠ 0 ∧
      N13IntegralInfinityReduction.reduceCoordinate d ≠ 0 ∧
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
        N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c := by
  obtain ⟨n, c, hc0, hc⟩ := exists_infinity_numerator a ha
  obtain ⟨m, d, hd0, hd⟩ := exists_infinity_numerator b hb
  refine ⟨N13IntegralInfinityChart.tClass ^ m * c,
    N13IntegralInfinityChart.tClass ^ n * d, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero m reduced_t_ne_zero) hc0
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n reduced_t_ne_zero) hd0
  · rw [map_mul, map_mul, map_pow, map_pow]
    calc
      N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          ((algebraMap B O N13IntegralInfinityChart.tClass) ^ n * algebraMap B O d) =
        (N13OrdinaryCurveOverlap.affineToInfinityOverlap a *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ n) * algebraMap B O d := by ring
      _ = algebraMap B O c * algebraMap B O d := by rw [hc]
      _ = (N13OrdinaryCurveOverlap.affineToInfinityOverlap b *
          (algebraMap B O N13IntegralInfinityChart.tClass) ^ m) * algebraMap B O c := by
        rw [hd]
        ring
      _ = N13OrdinaryCurveOverlap.affineToInfinityOverlap b *
          ((algebraMap B O N13IntegralInfinityChart.tClass) ^ m * algebraMap B O c) := by ring
end
end MazurProof.N13PrimitiveChartTransport
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13InvertibleReductionSaturation.instFactPrimeOfNatNat_fLT_1
theorem special_infinityPointIdeal_ne_bot (t v : N13GoodModelTwo.F2) :
    N13SpecialDivisorCharts.infinityPointIdeal t v ≠ ⊥ := by
  have hd : N13SpecialInfinityChart.curvePoly.degree ≠ 0 := by
    rw [degree_eq_natDegree N13SpecialInfinityChart.curvePoly_monic.ne_zero,
      N13SpecialInfinityChart.curvePoly_natDegree]
    norm_num
  have hn : N13SpecialInfinityChart.tClass -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ≠ 0 := by
    change algebraMap N13GoodModelTwo.F2[X] Bs X -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ≠ 0
    rw [← map_sub, ← map_zero (algebraMap N13GoodModelTwo.F2[X] Bs)]
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hd).ne (monic_X_sub_C t).ne_zero
  intro hbot
  have hm : N13SpecialInfinityChart.tClass -
      algebraMap N13GoodModelTwo.F2[X] Bs (C t) ∈
      N13SpecialDivisorCharts.infinityPointIdeal t v :=
    Ideal.subset_span (by simp)
  rw [hbot, Ideal.mem_bot] at hm
  exact hn hm
end InfinityApplication
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
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13InvertibleReductionSaturation.instFactPrimeOfNatNat_fLT_1
theorem special_point_infinityIdeal_ne_bot (p : N13SpecialDivisorCharts.CurvePoint) :
    (N13SpecialDivisorCharts.point p).infinityIdeal ≠ ⊥ := by
  cases p with
  | inl p =>
    unfold N13SpecialDivisorCharts.point
    by_cases hx : p.1.1 = 0
    · simp [hx, N13SpecialDivisorCharts.affineZeroPoint]
    · simp only [hx, N13SpecialDivisorCharts.affineOnePoint]
      exact special_infinityPointIdeal_ne_bot _ _
  | inr p =>
    unfold N13SpecialDivisorCharts.point
    exact special_infinityPointIdeal_ne_bot _ _
end InfinityApplication
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
theorem special_divisor_infinityIdeal_ne_bot
    (D : N13SpecialDivisorCharts.EffectiveDivisorTwo) :
    (N13SpecialDivisorCharts.ofDivisor D).infinityIdeal ≠ ⊥ := by
  refine Sym2.inductionOn D ?_
  intro p q
  change (N13SpecialDivisorCharts.point p).infinityIdeal *
    (N13SpecialDivisorCharts.point q).infinityIdeal ≠ ⊥
  intro h
  rcases Ideal.mul_eq_bot.mp h with hp | hq
  · exact special_point_infinityIdeal_ne_bot p hp
  · exact special_point_infinityIdeal_ne_bot q hq
end InfinityApplication
end
end MazurProof.N13InvertibleReductionSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveVerticalPresentation
noncomputable section
open scoped nonZeroDivisors
variable {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S]
/-- In a Noetherian domain, a nonzero element has a last divisible power
of a proper principal reduction kernel. The remaining factor has nonzero
reduction. The exponent and factor are actual witnesses. -/
theorem exists_primitive_factor
    (red : A →+* S) (p : A)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (z : A) (hz : z ≠ 0) :
    ∃ n : ℕ, ∃ a : A, red a ≠ 0 ∧ z = p ^ n * a := by
  classical
  have hproper : Ideal.span ({p} : Set A) ≠ ⊤ := by
    intro htop
    have hmem : (1 : A) ∈ RingHom.ker red := by
      rw [hker, htop]
      exact Submodule.mem_top
    have hzero := RingHom.mem_ker.mp hmem
    simpa using hzero
  have hex : ∃ n : ℕ, ¬p ^ n ∣ z := by
    by_contra h
    push_neg at h
    have hm : z ∈ ⨅ n : ℕ, Ideal.span ({p} : Set A) ^ n := by
      refine (Submodule.mem_iInf _).mpr fun n => ?_
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hproper, Ideal.mem_bot] at hm
    exact hz hm
  have hnondvd := Nat.find_spec hex
  have hnpos : 0 < Nat.find hex := by
    by_contra h
    have hnzero : Nat.find hex = 0 := by omega
    simp [hnzero] at hnondvd
  have hdvd : p ^ (Nat.find hex - 1) ∣ z := by
    by_contra h
    have hh := Nat.find_min' hex h
    omega
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨Nat.find hex - 1, a, ?_, ha⟩
  intro hared
  have hpa : p ∣ a := by
    have hh : a ∈ RingHom.ker red := RingHom.mem_ker.mpr hared
    rwa [hker, Ideal.mem_span_singleton] at hh
  obtain ⟨b, hb⟩ := hpa
  apply hnondvd
  refine ⟨b, ?_⟩
  have hn : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  calc
    z = p ^ (Nat.find hex - 1) * a := ha
    _ = p ^ (Nat.find hex - 1) * (p * b) := by rw [hb]
    _ = (p ^ (Nat.find hex - 1) * p) * b := by rw [mul_assoc]
    _ = p ^ (Nat.find hex - 1 + 1) * b := by
      rw [← pow_succ]
      <;> simp [Nat.succ_pred_eq_of_pos hnpos]
    _ = p ^ Nat.find hex * b := by rw [hn]
end
end MazurProof.N13PrimitiveVerticalPresentation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveVerticalPresentation
noncomputable section
open scoped nonZeroDivisors
variable {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
/-- Remove vertical powers from a numerator and denominator separately.
The displayed cross-multiplied equation records the exact normalization,
so no equality of fractions is silently changed. -/
theorem exists_primitive_fraction_presentation
    (red : A →+* S) (p : A)
    (hker : RingHom.ker red = Ideal.span ({p} : Set A))
    (f : K) (hf : f ≠ 0) :
    ∃ n m : ℕ, ∃ a b : A,
      red a ≠ 0 ∧ red b ≠ 0 ∧
      (algebraMap A K p) ^ m * f * algebraMap A K b =
        (algebraMap A K p) ^ n * algebraMap A K a := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective A f
  have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hx0 : x ≠ 0 := by
    intro hx
    apply hf
    rw [← hxy, hx, map_zero, zero_div]
  obtain ⟨n, a, ha, hxa⟩ := exists_primitive_factor red p hker x hx0
  obtain ⟨m, b, hb, hyb⟩ := exists_primitive_factor red p hker y hy0
  refine ⟨n, m, a, b, ha, hb, ?_⟩
  have hyK : algebraMap A K y ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hmul : f * algebraMap A K y = algebraMap A K x := by
    rw [← hxy, div_mul_cancel₀ _ hyK]
  rw [hxa, hyb, map_mul, map_mul, map_pow, map_pow] at hmul
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
end
end MazurProof.N13PrimitiveVerticalPresentation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveVerticalPresentation
noncomputable section
open scoped nonZeroDivisors
variable {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
section N13Charts
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveVerticalPresentation.instAlgebraAffineRationalRing MazurProof.N13PrimitiveVerticalPresentation.instIsFractionRingAffineCommonField
/-- Every nonzero N13 common-field function has primitive affine numerator
and denominator, with the exact removed powers of two recorded. -/
theorem exists_affine_primitive_fraction_presentation (f : CommonField) (hf : f ≠ 0) :
    ∃ n m : ℕ, ∃ a b : Affine,
      N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0 ∧
      N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0 ∧
      (algebraMap Affine CommonField 2) ^ m * f * algebraMap Affine CommonField b =
        (algebraMap Affine CommonField 2) ^ n * algebraMap Affine CommonField a := by
  simpa only [N13GeneralizedMumfordReduction.ker_reduceCoordinate] using
    exists_primitive_fraction_presentation
      N13GeneralizedMumfordReduction.reduceCoordinate 2
      N13GeneralizedMumfordReduction.ker_reduceCoordinate f hf
end N13Charts
end
end MazurProof.N13PrimitiveVerticalPresentation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalBranchIdeals
noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalBranchIdeals.instAlgebraAR
/-- The affine principal relation and its positive orientation force BOTH
actual branch ideal equations for the transported common numerator and
denominator. The negative equation is derived from the norm/degree theorem;
it is not an additional compatibility hypothesis. -/
theorem tensor_branch_ideal_equations
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (h₀ : EffectiveChamber E₀) (h₁ : EffectiveChamber E₁)
    (h₂ : EffectiveChamber E₂) (h₃ : EffectiveChamber E₃)
    (L₀ L₁ L₂ L₃ : N13TwoChartPicardRealization.Line)
    (hL₀ : HasInfinityMultiplicities L₀ (positiveMultiplicity E₀) (negativeMultiplicity E₀))
    (hL₁ : HasInfinityMultiplicities L₁ (positiveMultiplicity E₁) (negativeMultiplicity E₁))
    (hL₂ : HasInfinityMultiplicities L₂ (positiveMultiplicity E₂) (negativeMultiplicity E₂))
    (hL₃ : HasInfinityMultiplicities L₃ (positiveMultiplicity E₃) (negativeMultiplicity E₃))
    (f : Fˣ) (n m : ℕ) (a b : A) (c d : B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c)
    (hprincipal :
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₀ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₁ *
        toPrincipalIdeal R F f =
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₂ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₃)
    (horientation : E₀.nInf + E₁.nInf +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf) :
    Ideal.map positiveExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map positiveExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) ∧
    Ideal.map negativeExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map negativeExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) := by
  exact HuangN13.N13PrincipalBranchIdeals.tensor_branch_ideal_equations E₀ E₁ E₂ E₃ h₀ h₁ h₂ h₃ L₀ L₁ L₂ L₃ hL₀ hL₁ hL₂ hL₃ f n m a b c d hb hc hd hf hcross hprincipal horientation
end
end MazurProof.N13PrincipalBranchIdeals
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrimitiveAffineComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InvertibleReductionSaturation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR MazurProof.N13PrimitiveAffineComparison.instIsLocalizationIntegralRingVerticalScalarsR
theorem integral_cleared_equation
    (L M : Line)
    (hL : AffineVerticallySaturated L) (hM : AffineVerticallySaturated M)
    (f : Fˣ) (n m : ℕ) (a b : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hprincipal : genericIdealUnit L * toPrincipalIdeal R F f = genericIdealUnit M) :
    Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal := by
  exact HuangN13.N13PrimitiveAffineComparison.integral_cleared_equation L M hL hM f n m a b ha hb hf hprincipal
end
end MazurProof.N13PrimitiveAffineComparison
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
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem data_infinity_reduction_ne_bot (D : Data) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate D.charts.infinityIdeal ≠ ⊥ := by
  change (N13TwoChartSpecialRestriction.restrict D.charts).infinityIdeal ≠ ⊥
  rw [D.special_infinity]
  exact N13InvertibleReductionSaturation.special_divisor_infinityIdeal_ne_bot D.specialDivisor
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
open N13InfinityChartMarking hiding Line B QP
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
  exact HuangN13.N13IntegralPrincipalComparison.integral_infinity_cleared_equation L M a b c d hb hc hd hL hM haffine hcross hplus hminus
end
end MazurProof.N13IntegralPrincipalComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedTensorComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem genericIdealUnit_tensor (L M : Line) :
    genericIdealUnit (tensor L M) = genericIdealUnit L * genericIdealUnit M := by
  apply Units.ext
  simp only [coe_genericIdealUnit, N13TwoChartLineTensor.tensor_affineIdeal,
    Ideal.map_mul, FractionalIdeal.coeIdeal_mul, Units.val_mul]
end
end MazurProof.N13MarkedTensorComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedTensorComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Extract the actual affine principal multiplier and its positive order
from equality in the existing oriented quotient. -/
theorem exists_multiplier_of_class_sum_eq
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (D₀ D₁ D₂ D₃ : Data)
    (hraw₀ : genericRaw D₀.charts D₀.infinityOrder = SexticMumford.semiMumfordRaw Model E₀)
    (hraw₁ : genericRaw D₁.charts D₁.infinityOrder = SexticMumford.semiMumfordRaw Model E₁)
    (hraw₂ : genericRaw D₂.charts D₂.infinityOrder = SexticMumford.semiMumfordRaw Model E₂)
    (hraw₃ : genericRaw D₃.charts D₃.infinityOrder = SexticMumford.semiMumfordRaw Model E₃)
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    ∃ f : Fˣ,
      SexticMumford.mumfordIdealUnit Model E₀ * SexticMumford.mumfordIdealUnit Model E₁ *
          toPrincipalIdeal R F f =
        SexticMumford.mumfordIdealUnit Model E₂ * SexticMumford.mumfordIdealUnit Model E₃ ∧
      E₀.nInf + E₁.nInf +
          Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf := by
  let q := QuotientGroup.mk'
    (SexticMumford.principalOriented Model (N13Infinity.positiveInfinityOrder Q₂)).range
  have hq : q (SexticMumford.semiMumfordRaw Model E₀ * SexticMumford.semiMumfordRaw Model E₁) =
      q (SexticMumford.semiMumfordRaw Model E₂ * SexticMumford.semiMumfordRaw Model E₃) := by
    change q (genericRaw D₀.charts D₀.infinityOrder) * q (genericRaw D₁.charts D₁.infinityOrder) =
      q (genericRaw D₂.charts D₂.infinityOrder) * q (genericRaw D₃.charts D₃.infinityOrder) at hclass
    rw [hraw₀, hraw₁, hraw₂, hraw₃] at hclass
    simpa only [map_mul] using hclass
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at hq
  rw [QuotientGroup.mk'_eq_mk'] at hq
  obtain ⟨z, hz, hmul⟩ := hq
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hz
  refine ⟨f, congrArg Prod.fst hmul, ?_⟩
  have hi := congrArg
    (fun z : SexticMumford.OrientedFrac Model => Multiplicative.toAdd z.2) hmul
  change ((E₀.nInf - 1) + (E₁.nInf - 1)) +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
    (E₂.nInf - 1) + (E₃.nInf - 1) at hi
  omega
end
end MazurProof.N13MarkedTensorComparison
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedTensorComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveVerticalPresentation.instAlgebraAffineRationalRing MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13MarkedTensorComparison.instAlgebraAR
/-- The central tensor-normalization construction for the marked effective
representatives. All four regular functions, nonzero reductions, both ideal
equations, and the single common overlap fraction are constructed. -/
theorem exists_integral_tensor_comparison
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (h₀ : EffectiveChamber E₀) (h₁ : EffectiveChamber E₁)
    (h₂ : EffectiveChamber E₂) (h₃ : EffectiveChamber E₃)
    (D₀ D₁ D₂ D₃ : Data)
    (hraw₀ : genericRaw D₀.charts D₀.infinityOrder = SexticMumford.semiMumfordRaw Model E₀)
    (hraw₁ : genericRaw D₁.charts D₁.infinityOrder = SexticMumford.semiMumfordRaw Model E₁)
    (hraw₂ : genericRaw D₂.charts D₂.infinityOrder = SexticMumford.semiMumfordRaw Model E₂)
    (hraw₃ : genericRaw D₃.charts D₃.infinityOrder = SexticMumford.semiMumfordRaw Model E₃)
    (hs₀ : AffineVerticallySaturated D₀.charts) (hs₁ : AffineVerticallySaturated D₁.charts)
    (hs₂ : AffineVerticallySaturated D₂.charts) (hs₃ : AffineVerticallySaturated D₃.charts)
    (hm₀ : HasInfinityMultiplicities D₀.charts (positiveMultiplicity E₀) (negativeMultiplicity E₀))
    (hm₁ : HasInfinityMultiplicities D₁.charts (positiveMultiplicity E₁) (negativeMultiplicity E₁))
    (hm₂ : HasInfinityMultiplicities D₂.charts (positiveMultiplicity E₂) (negativeMultiplicity E₂))
    (hm₃ : HasInfinityMultiplicities D₃.charts (positiveMultiplicity E₃) (negativeMultiplicity E₃))
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)) := by
  obtain ⟨f, hprincipal, horientation⟩ := exists_multiplier_of_class_sum_eq
    E₀ E₁ E₂ E₃ D₀ D₁ D₂ D₃ hraw₀ hraw₁ hraw₂ hraw₃ hclass
  obtain ⟨n, m, a, b, ha, hb, hf⟩ :=
    N13PrimitiveVerticalPresentation.exists_affine_primitive_fraction_presentation (f : F) f.ne_zero
  obtain ⟨c, d, hc, hd, hcross⟩ :=
    N13PrimitiveChartTransport.exists_common_primitive_presentation a b ha hb
  have hb0 : b ≠ 0 := fun h => hb (by simp [h])
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hd0 : d ≠ 0 := fun h => hd (by simp [h])
  have hf' : 2 ^ m * (f : F) * algebraMap A F b = 2 ^ n * algebraMap A F a := by
    simpa only [map_ofNat] using hf
  have hgeneric : genericIdealUnit (tensor D₀.charts D₁.charts) * toPrincipalIdeal R F f =
      genericIdealUnit (tensor D₂.charts D₃.charts) := by
    rw [genericIdealUnit_tensor, genericIdealUnit_tensor]
    have hu₀ := congrArg Prod.fst hraw₀
    have hu₁ := congrArg Prod.fst hraw₁
    have hu₂ := congrArg Prod.fst hraw₂
    have hu₃ := congrArg Prod.fst hraw₃
    change genericIdealUnit D₀.charts = SexticMumford.mumfordIdealUnit Model E₀ at hu₀
    change genericIdealUnit D₁.charts = SexticMumford.mumfordIdealUnit Model E₁ at hu₁
    change genericIdealUnit D₂.charts = SexticMumford.mumfordIdealUnit Model E₂ at hu₂
    change genericIdealUnit D₃.charts = SexticMumford.mumfordIdealUnit Model E₃ at hu₃
    rw [hu₀, hu₁, hu₂, hu₃]
    exact hprincipal
  have haffine := N13PrimitiveAffineComparison.integral_cleared_equation
    (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)
    (N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _ hs₀ hs₁)
    (N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _ hs₂ hs₃)
    f n m a b ha hb hf' hgeneric
  obtain ⟨hplus, hminus⟩ := tensor_branch_ideal_equations
    E₀ E₁ E₂ E₃ h₀ h₁ h₂ h₃ D₀.charts D₁.charts D₂.charts D₃.charts
    hm₀ hm₁ hm₂ hm₃ f n m a b c d hb0 hc0 hd0 hf' hcross hprincipal horientation
  have htensor (D E : Data) :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate (tensor D.charts E.charts).infinityIdeal ≠ ⊥ := by
    rw [N13TwoChartLineTensor.tensor_infinityIdeal, Ideal.map_mul]
    intro h
    rcases Ideal.mul_eq_bot.mp h with hD | hE
    · exact data_infinity_reduction_ne_bot D hD
    · exact data_infinity_reduction_ne_bot E hE
  have hinfinity := integral_infinity_cleared_equation
    (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)
    a b c d hb0 hc hd (htensor D₀ D₁) (htensor D₂ D₃)
    haffine hcross hplus hminus
  exact ⟨{
    aNum := a
    aDen := b
    iNum := c
    iDen := d
    aNum_ne := ha
    aDen_ne := hb
    iNum_ne := hc
    iDen_ne := hd
    affine_eq := haffine
    infinity_eq := hinfinity
    overlap_eq := hcross }⟩
end
end MazurProof.N13MarkedTensorComparison
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (E₀ E₁ E₂ E₃ : MazurProof.N13Mumford.SemiMumford MazurProof.N13OverlapBranchCompatibility.Q₂)
    (h₀ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₀) (h₁ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₁)
    (h₂ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₂) (h₃ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₃)
    (D₀ D₁ D₂ D₃ : MazurProof.N13TwoChartPicardRealization.Data)
    (hraw₀ : MazurProof.N13TwoChartPicardRealization.genericRaw D₀.charts D₀.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₀)
    (hraw₁ : MazurProof.N13TwoChartPicardRealization.genericRaw D₁.charts D₁.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₁)
    (hraw₂ : MazurProof.N13TwoChartPicardRealization.genericRaw D₂.charts D₂.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₂)
    (hraw₃ : MazurProof.N13TwoChartPicardRealization.genericRaw D₃.charts D₃.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₃)
    (hs₀ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₀.charts) (hs₁ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₁.charts)
    (hs₂ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₂.charts) (hs₃ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₃.charts)
    (hm₀ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₀.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₀) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₀))
    (hm₁ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₁.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₁) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₁))
    (hm₂ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₂.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₂) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₂))
    (hm₃ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₃.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₃) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₃))
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (MazurProof.N13CoherentChartComparison.IntegralComparison
      (MazurProof.N13MarkedTensorComparison.tensor D₀.charts D₁.charts) (MazurProof.N13MarkedTensorComparison.tensor D₂.charts D₃.charts)) := by
  exact MazurProof.N13MarkedTensorComparison.exists_integral_tensor_comparison E₀ E₁ E₂ E₃ h₀ h₁ h₂ h₃ D₀ D₁ D₂ D₃ hraw₀ hraw₁ hraw₂ hraw₃ hs₀ hs₁ hs₂ hs₃ hm₀ hm₁ hm₂ hm₃ hclass
