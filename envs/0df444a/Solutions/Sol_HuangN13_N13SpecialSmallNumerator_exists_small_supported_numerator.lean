-- Prove2me | solution 1 for HuangN13.N13SpecialSmallNumerator.exists_small_supported_numerator
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:25:23.789826+00:00
-- url     : https://prove2.me/submissions/7fdbd050-4c5b-4f05-b98a-37f08342cd1c

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Theorems.Thm_HuangN13_N13SpecialLaurentBranches_degree_four_polynomial_bounds
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13SpecialAffineNorm_conjugate_linear
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityCoeffMap_hPoly

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
@[simp] lemma order_parameter : (parameter K).order = 1 := by
  simp [parameter, HahnSeries.order_single]
end
end N13LaurentPolynomialOrder
end MazurProof
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_xClass :
    affineToInfinityOverlap xClass = xOverlap := by
  simp [affineToInfinityOverlap, xClass,
    N13GoodCoordinateRingTwo.xClass,
    N13GoodCoordinateRingTwo.mk, affineCoeffMap]
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
theorem affine_xClass_mapsToUnit :
    IsUnit (affineToInfinityOverlap xClass) := by
  rw [affineToInfinityOverlap_xClass]
  exact xOverlap_isUnit
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
/-- The induced restriction from the affine principal open to the infinity
principal open. -/
def affineOverlapToInfinityOverlap :
    AffineOverlap →+* InfinityOverlap :=
  IsLocalization.Away.lift xClass affine_xClass_mapsToUnit
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
@[simp] theorem affineOverlapToInfinityOverlap_algebraMap
    (z : AffineCurve) :
    affineOverlapToInfinityOverlap
        (algebraMap AffineCurve AffineOverlap z) =
      affineToInfinityOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      xClass affine_xClass_mapsToUnit z
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
@[simp] theorem affineOverlapToInfinityOverlap_xAffineOverlap :
    affineOverlapToInfinityOverlap xAffineOverlap = xOverlap := by
  rw [xAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_xClass]
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
@[simp] theorem affineOverlapToInfinityOverlap_yAffineOverlap :
    affineOverlapToInfinityOverlap yAffineOverlap =
      xOverlap ^ 3 * vOverlap := by
  rw [yAffineOverlap,
    affineOverlapToInfinityOverlap_algebraMap,
    affineToInfinityOverlap_yClass]
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₀_constant : PowerSeries.constantCoeff r₀ = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.map PadicInt.toZMod
    N13FormalInfinityBranches.branchZero) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff, map_zero]
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_constant : PowerSeries.constantCoeff r₁ = 1 := by
  rw [r₁_eq]
  norm_num [h, r₀_constant]
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem root_eval (r : P) (hr : r ^ 2 + h * r - rhs = 0) :
    N13SpecialInfinityChart.curvePoly.eval₂ beta r = 0 := by
  simpa [N13SpecialInfinityChart.curvePoly, N13SpecialInfinityChart.hPoly,
    N13SpecialInfinityChart.rhsPoly, beta, h, rhs, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hr
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def plus : B →+* P := AdjoinRoot.lift beta r₀ (root_eval r₀ r₀_relation)
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def minus : B →+* P := AdjoinRoot.lift beta r₁ (root_eval r₁ r₁_relation)
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem plus_base (p : K[X]) :
    plus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem minus_base (p : K[X]) :
    minus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem plus_t : plus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (plus_base X).trans (by simp [beta])
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem minus_t : minus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (minus_base X).trans (by simp [beta])
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem plus_v : plus N13SpecialInfinityChart.vClass = r₀ :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem minus_v : minus N13SpecialInfinityChart.vClass = r₁ :=
  AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem span_pair_eq_top_of_right_unit (x y : P) (hy : IsUnit y) :
    Ideal.span ({x, y} : Set P) = ⊤ := by
  obtain ⟨u, hu⟩ := hy
  rw [← hu, Ideal.eq_top_iff_one]
  have hm : (u : P) ∈ Ideal.span ({x, (u : P)} : Set P) := Ideal.subset_span (by simp)
  have hh := Ideal.mul_mem_left (Ideal.span ({x, (u : P)} : Set P)) (↑(u⁻¹) : P) hm
  simpa using hh
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
/-- The positive special point has order one on its own branch. -/
theorem plus_positive_point :
    Ideal.map plus (N13SpecialDivisorCharts.infinityPointIdeal 0 0) =
      Ideal.span ({PowerSeries.X} : Set P) := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0,
    map_zero, sub_zero, Ideal.map_span, Set.image_pair, plus_t, plus_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  exact PowerSeries.X_dvd_iff.mpr r₀_constant
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
/-- The positive special point is absent from the other branch. -/
theorem minus_positive_point :
    Ideal.map minus (N13SpecialDivisorCharts.infinityPointIdeal 0 0) = ⊤ := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0,
    map_zero, sub_zero, Ideal.map_span, Set.image_pair, minus_t, minus_v]
  apply span_pair_eq_top_of_right_unit
  rw [PowerSeries.isUnit_iff_constantCoeff, r₁_constant]
  exact isUnit_one
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
/-- The negative special point is absent from the positive branch. -/
theorem plus_negative_point :
    Ideal.map plus (N13SpecialDivisorCharts.infinityPointIdeal 0 1) = ⊤ := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0, Polynomial.C_1,
    map_zero, map_one, sub_zero, Ideal.map_span, Set.image_pair, map_sub, plus_t, plus_v]
  apply span_pair_eq_top_of_right_unit
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_one, r₀_constant, zero_sub]
  exact isUnit_neg_one
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
/-- The negative special point has order one on its own branch. -/
theorem minus_negative_point :
    Ideal.map minus (N13SpecialDivisorCharts.infinityPointIdeal 0 1) =
      Ideal.span ({PowerSeries.X} : Set P) := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0, Polynomial.C_1,
    map_zero, map_one, sub_zero, Ideal.map_span, Set.image_pair, map_sub, minus_t, minus_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  apply PowerSeries.X_dvd_iff.mpr
  simp only [map_sub, map_one, r₁_constant, sub_self]
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem pointPolynomial_monic (P : CurvePoint) : (pointPolynomial P).Monic := by
  cases P
  · exact monic_X_sub_C _
  · exact monic_one
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem pointPolynomial_mem (P : CurvePoint) : xClass (pointPolynomial P) ∈ (point P).affineIdeal := by
  cases P with
  | inl P =>
    simp only [point]
    split_ifs with hx
    · exact N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal (X - C P.1.1) (C P.1.2)
    · exact N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal (X - C P.1.1) (C P.1.2)
  | inr P => exact Submodule.mem_top
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
@[simp] theorem divisorPolynomial_mk (P Q : CurvePoint) :
    divisorPolynomial s(P, Q) = pointPolynomial P * pointPolynomial Q := rfl
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem divisorPolynomial_monic (D : EffectiveDivisorTwo) : (divisorPolynomial D).Monic := by
  refine Sym2.inductionOn D ?_
  intro P Q
  exact (pointPolynomial_monic P).mul (pointPolynomial_monic Q)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem divisorPolynomial_mem (D : EffectiveDivisorTwo) :
    xClass (divisorPolynomial D) ∈ (ofDivisor D).affineIdeal := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change xClass (pointPolynomial P * pointPolynomial Q) ∈
    (point P).affineIdeal * (point Q).affineIdeal
  simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
  exact Ideal.mul_mem_mul (pointPolynomial_mem P) (pointPolynomial_mem Q)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem tensorPolynomial_monic (D E : EffectiveDivisorTwo) : (tensorPolynomial D E).Monic :=
  (divisorPolynomial_monic D).mul (divisorPolynomial_monic E)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem tensorPolynomial_mem (D E : EffectiveDivisorTwo) :
    xClass (tensorPolynomial D E) ∈ (tensor (ofDivisor D) (ofDivisor E)).affineIdeal := by
  change xClass (divisorPolynomial D * divisorPolynomial E) ∈
    (ofDivisor D).affineIdeal * (ofDivisor E).affineIdeal
  simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
  exact Ideal.mul_mem_mul (divisorPolynomial_mem D) (divisorPolynomial_mem E)
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem pointPolynomial_fibres (P : CurvePoint) :
    ∃ i j : ℕ, i + j ≤ 1 ∧ pointPolynomial P = X ^ i * (X - 1) ^ j := by
  cases P with
  | inl P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1.1 (ZMod.pow_card P.1.1) with hx | hx
    · exact ⟨1, 0, by decide, by simp [pointPolynomial, hx]⟩
    · exact ⟨0, 1, by decide, by simp [pointPolynomial, hx]⟩
  | inr P => exact ⟨0, 0, by decide, by simp [pointPolynomial]⟩
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem divisorPolynomial_fibres (D : EffectiveDivisorTwo) :
    ∃ i j : ℕ, i + j ≤ 2 ∧ divisorPolynomial D = X ^ i * (X - 1) ^ j := by
  refine Sym2.inductionOn D ?_
  intro P Q
  obtain ⟨i, j, hij, hp⟩ := pointPolynomial_fibres P
  obtain ⟨k, l, hkl, hq⟩ := pointPolynomial_fibres Q
  refine ⟨i + k, j + l, by omega, ?_⟩
  rw [divisorPolynomial_mk, hp, hq, pow_add, pow_add]
  ring
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
theorem tensorPolynomial_fibres (D E : EffectiveDivisorTwo) :
    ∃ i j : ℕ, i + j ≤ 4 ∧ tensorPolynomial D E = X ^ i * (X - 1) ^ j := by
  obtain ⟨i, j, hij, hd⟩ := divisorPolynomial_fibres D
  obtain ⟨k, l, hkl, he⟩ := divisorPolynomial_fibres E
  refine ⟨i + k, j + l, by omega, ?_⟩
  rw [tensorPolynomial, hd, he, pow_add, pow_add]
  ring
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
/-- The full special comparison, rather than an arbitrary guessed small
function, supplies the regular factor pair and the exact two cross-products. -/
theorem exists_factor_pair_of_comparison
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ z w : R,
      z ∈ (tensor (ofDivisor F) (ofDivisor H)).affineIdeal ∧
      w ∈ (tensor (ofDivisor D) (ofDivisor E)).affineIdeal ∧
      h.aNum * xClass (tensorPolynomial D E) = h.aDen * z ∧
      h.aDen * xClass (tensorPolynomial F H) = h.aNum * w ∧
      z * w = xClass (tensorPolynomial D E * tensorPolynomial F H) ∧ z ≠ 0 ∧ w ≠ 0 := by
  have hz : h.aNum * xClass (tensorPolynomial D E) ∈
      Ideal.span ({h.aDen} : Set R) * (tensor (ofDivisor F) (ofDivisor H)).affineIdeal := by
    rw [← h.affine_eq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨_, tensorPolynomial_mem D E, rfl⟩
  have hw : h.aDen * xClass (tensorPolynomial F H) ∈
      Ideal.span ({h.aNum} : Set R) * (tensor (ofDivisor D) (ofDivisor E)).affineIdeal := by
    rw [h.affine_eq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨_, tensorPolynomial_mem F H, rfl⟩
  obtain ⟨z, hzmem, hzeq⟩ := Ideal.mem_span_singleton_mul.mp hz
  obtain ⟨w, hwmem, hweq⟩ := Ideal.mem_span_singleton_mul.mp hw
  have hprod : z * w = xClass (tensorPolynomial D E * tensorPolynomial F H) := by
    apply mul_left_cancel₀ (mul_ne_zero h.aNum_ne h.aDen_ne)
    simp only [xClass, N13GoodCoordinateRingTwo.xClass_mul]
    calc
      (h.aNum * h.aDen) * (z * w) = (h.aDen * z) * (h.aNum * w) := by ring
      _ = (h.aNum * xClass (tensorPolynomial D E)) *
          (h.aDen * xClass (tensorPolynomial F H)) := by rw [hzeq, hweq]
      _ = _ := by ring
  have hnonzero : z * w ≠ 0 := by
    rw [hprod]
    exact N13GoodCoordinateRingTwo.xClass_ne_zero
      (mul_ne_zero (tensorPolynomial_monic D E).ne_zero (tensorPolynomial_monic F H).ne_zero)
  exact ⟨z, w, hzmem, hwmem, hzeq.symm, hweq.symm, hprod,
    left_ne_zero_of_mul hnonzero, right_ne_zero_of_mul hnonzero⟩
end
end MazurProof.N13SpecialComparisonFactorPair
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
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K
@[simp] theorem conjugate_xClass (p : K[X]) : conjugate (xClass p) = xClass p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialAffineNorm
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
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K
theorem xClass_injective : Function.Injective xClass := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra h
  apply xClass_ne_zero h
  rw [xClass_sub, hpq, sub_self]
end
end MazurProof.N13SpecialAffineNorm
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
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K
theorem norm_mul (z w : R) : norm (z * w) = norm z * norm w := by
  apply xClass_injective
  rw [xClass_mul, ← mul_conjugate, ← mul_conjugate, ← mul_conjugate, map_mul]
  ring
end
end MazurProof.N13SpecialAffineNorm
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
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K
theorem norm_xClass (p : K[X]) : norm (xClass p) = p ^ 2 := by
  apply xClass_injective
  rw [← mul_conjugate, conjugate_xClass, xClass_pow, pow_two]
end
end MazurProof.N13SpecialAffineNorm
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
namespace MazurProof.N13SpecialAffineNorm
noncomputable section
open Polynomial N13GoodCoordinateRingTwo
open N13SpecialDivisorCharts hiding K
open N13SpecialComparisonFactorPair hiding xClass R
/-- The arbitrary comparison already forces the cleared numerator norm to
divide a polynomial with support only at the two finite rational fibres.
No enumeration or principal-code compatibility is used. -/
theorem exists_factor_pair_with_supported_norm
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ z w : R, ∃ i j : ℕ,
      i + j ≤ 16 ∧ z ≠ 0 ∧ w ≠ 0 ∧
      h.aNum * xClass (tensorPolynomial D E) = h.aDen * z ∧
      h.aDen * xClass (tensorPolynomial F H) = h.aNum * w ∧
      norm z * norm w = X ^ i * (X - 1) ^ j ∧
      norm z ∣ X ^ i * (X - 1) ^ j := by
  obtain ⟨z, w, _, _, hz, hw, hprod, hz0, hw0⟩ := exists_factor_pair_of_comparison D E F H h
  obtain ⟨i, j, hij, hleft⟩ := tensorPolynomial_fibres D E
  obtain ⟨k, l, hkl, hright⟩ := tensorPolynomial_fibres F H
  have hn : norm z * norm w = X ^ (2 * (i + k)) * (X - 1) ^ (2 * (j + l)) := by
    rw [← norm_mul, hprod, norm_xClass, hleft, hright]
    rw [Nat.mul_comm 2 (i + k), Nat.mul_comm 2 (j + l), pow_mul, pow_mul, pow_add, pow_add]
    ring
  refine ⟨z, w, 2 * (i + k), 2 * (j + l), by omega, hz0, hw0, hz, hw, hn, ?_⟩
  exact ⟨norm w, hn.symm⟩
end
end MazurProof.N13SpecialAffineNorm
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_xClass (p : K[X]) : plus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_xClass (p : K[X]) : minus (N13GoodCoordinateRingTwo.xClass p) = base p :=
  AdjoinRoot.lift_of _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem plus_yClass : plus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
@[simp] theorem minus_yClass : minus N13GoodCoordinateRingTwo.yClass =
    t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁ := AdjoinRoot.lift_root _
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

theorem y_branch_sum : plus N13GoodCoordinateRingTwo.yClass + minus N13GoodCoordinateRingTwo.yClass =
    -base N13GoodCoordinateRingTwo.hPoly := by
  rw [plus_yClass, minus_yClass, N13SpecialInfinityBranchJets.r₁_eq, map_sub, map_neg]
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh]
  simp only [N13GoodCoordinateRingTwo.hPoly, map_add, map_pow, map_one, base_X]
  change t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀ +
      t⁻¹ ^ 3 * (-(1 + t ^ 2 + t ^ 3) - includeSeries N13SpecialInfinityBranchJets.r₀) =
    -(t⁻¹ ^ 3 + t⁻¹ + 1)
  field_simp [t_ne_zero]
  ring
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem plus_conjugate (z : R) : plus (N13SpecialAffineNorm.conjugate z) = minus z := by
  have hz : z = N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) :=
    (N13GoodCoordinateRingTwo.recompose z).symm
  rw [hz, N13SpecialAffineNorm.conjugate_linear]
  simp only [N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, minus_xClass,
    map_sub, map_neg]
  linear_combination -(base (N13GoodCoordinateRingTwo.coeffY z)) * y_branch_sum
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem branch_product (z : R) : plus z * minus z = base (N13SpecialAffineNorm.norm z) := by
  rw [← plus_conjugate, ← map_mul, N13SpecialAffineNorm.mul_conjugate, plus_xClass]
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem plus_ne_zero (z : R) (hz : z ≠ 0) : plus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact left_ne_zero_of_mul hn
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem minus_ne_zero (z : R) (hz : z ≠ 0) : minus z ≠ 0 := by
  have hn := N13BranchNorm.evalPoly_ne_zero K (N13SpecialAffineNorm.norm_ne_zero z hz)
  rw [← branch_product] at hn
  exact right_ne_zero_of_mul hn
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem include_order_nonnegative (r : P) : 0 ≤ (includeSeries r).order := by
  by_cases hr : r = 0
  · simp [hr]
  · have hinc : includeSeries r ≠ 0 :=
      (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hr
    rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((r : LaurentSeries K).coeff j) = 0
    rw [PowerSeries.coeff_coe, if_pos hj]
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem degree_four_polynomial_bounds (p q : K[X])
    (hpoles : (-4 : ℤ) ≤ (plus (N13SpecialAffineNorm.linear p q)).order)
    (hmoles : (-4 : ℤ) ≤ (minus (N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 := by
  exact HuangN13.N13SpecialLaurentBranches.degree_four_polynomial_bounds p q hpoles hmoles
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def infinityBranch (negative : Bool) : B →+* P :=
  if negative then N13SpecialInfinityBranchJets.minus else N13SpecialInfinityBranchJets.plus
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def affineBranch (negative : Bool) : R →+* L := if negative then minus else plus
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem branch_base (negative : Bool) (p : K[X]) :
    includeSeries (infinityBranch negative (algebraMap K[X] B p)) =
      p.eval₂ (algebraMap K L) t := by
  cases negative
  · change includeSeries (N13SpecialInfinityBranchJets.plus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.plus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
  · change includeSeries (N13SpecialInfinityBranchJets.minus
      (N13IntegralInfinityReduction.specialBaseClass p)) = _
    rw [N13SpecialInfinityBranchJets.minus_base, N13SpecialInfinityBranchJets.beta_eq_coe]
    exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
private theorem t_isUnit (negative : Bool) :
    IsUnit ((includeSeries.comp (infinityBranch negative)) N13SpecialInfinityChart.tClass) := by
  change IsUnit (includeSeries (infinityBranch negative (algebraMap K[X] B X)))
  rw [branch_base]
  simpa using (isUnit_iff_ne_zero.mpr t_ne_zero : IsUnit t)
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def overlapBranch (negative : Bool) : O →+* L :=
  IsLocalization.Away.lift N13SpecialInfinityChart.tClass (t_isUnit negative)
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_infinity (negative : Bool) (b : B) :
    overlapBranch negative (algebraMap B O b) = includeSeries (infinityBranch negative b) :=
  DFunLike.congr_fun
    (IsLocalization.Away.lift_comp N13SpecialInfinityChart.tClass (t_isUnit negative)) b
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_t (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.tOverlap = t := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B X)) = _
  rw [overlapBranch_infinity, branch_base]
  simp
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_x (negative : Bool) :
    overlapBranch negative N13SpecialCurveOverlap.xOverlap = t⁻¹ := by
  have he := congrArg (overlapBranch negative) N13SpecialCurveOverlap.tOverlap_mul_xOverlap
  rw [map_mul, overlapBranch_t, map_one] at he
  apply mul_left_cancel₀ t_ne_zero
  rw [he, mul_inv_cancel₀ t_ne_zero]
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem overlapBranch_coefficient (negative : Bool) (a : K) :
    overlapBranch negative (N13SpecialCurveOverlap.coefficientToInfinityOverlap a) =
      algebraMap K L a := by
  change overlapBranch negative (algebraMap B O (algebraMap K[X] B (C a))) = _
  rw [overlapBranch_infinity, branch_base]
  simp
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
private theorem base_X' : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem overlapBranch_affine_hom (negative : Bool) :
    (overlapBranch negative).comp N13SpecialCurveOverlap.affineToInfinityOverlap =
      affineBranch negative := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap
          (AdjoinRoot.of N13GoodCoordinateRingTwo.curvePoly (C a))) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass (C a))
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_of]
      simp only [N13SpecialCurveOverlap.affineCoeffMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [overlapBranch_coefficient]
      cases negative <;> simp [affineBranch, base, N13BranchNorm.evalPoly]
    · change overlapBranch negative
        (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.xClass) =
        affineBranch negative (N13GoodCoordinateRingTwo.xClass X)
      rw [N13SpecialCurveOverlap.affineToInfinityOverlap_xClass, overlapBranch_x]
      cases negative
      · simp only [affineBranch, Bool.false_eq_true, if_false, plus_xClass, base_X']
      · simp only [affineBranch, if_true, minus_xClass, base_X']
  · change overlapBranch negative
      (N13SpecialCurveOverlap.affineToInfinityOverlap N13SpecialCurveOverlap.yClass) =
      affineBranch negative N13GoodCoordinateRingTwo.yClass
    rw [N13SpecialCurveOverlap.affineToInfinityOverlap_yClass]
    change overlapBranch negative (N13SpecialCurveOverlap.xOverlap ^ 3 *
      algebraMap B O N13SpecialInfinityChart.vClass) = _
    rw [map_mul, map_pow, overlapBranch_x, overlapBranch_infinity]
    cases negative
    · simp only [affineBranch, infinityBranch, Bool.false_eq_true, if_false, plus_yClass,
        N13SpecialInfinityBranchJets.plus_v]
    · simp only [affineBranch, infinityBranch, if_true, minus_yClass,
        N13SpecialInfinityBranchJets.minus_v]
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
@[simp] theorem overlapBranch_affine (negative : Bool) (a : R) :
    overlapBranch negative (N13SpecialCurveOverlap.affineToInfinityOverlap a) =
      affineBranch negative a := DFunLike.congr_fun (overlapBranch_affine_hom negative) a
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
theorem cross_relation (negative : Bool) (a b : R) (c d : B)
    (h : N13SpecialCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13SpecialCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    affineBranch negative a * includeSeries (infinityBranch negative d) =
      affineBranch negative b * includeSeries (infinityBranch negative c) := by
  simpa only [map_mul, overlapBranch_affine, overlapBranch_infinity] using
    congrArg (overlapBranch negative) h
end
end MazurProof.N13SpecialOverlapBranches
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem affineBranch_injective (negative : Bool) : Function.Injective (affineBranch negative) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra h
  have hn : affineBranch negative (a - b) ≠ 0 := by
    cases negative
    · exact plus_ne_zero _ h
    · exact minus_ne_zero _ h
  apply hn
  simp only [map_sub, hab, sub_self]
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
private theorem localization_hom_injective
    {A S T : Type*} [CommRing A] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (f : S →+* T) (hf : Function.Injective (f.comp (algebraMap A S))) :
    Function.Injective f := by
  have hzero (z : S) (hz : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M z
    have hfa : f (algebraMap A S a) = 0 := by rw [← ha, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hf (by simpa using hfa)
    rw [ha0, map_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right (IsLocalization.map_units S s).ne_zero
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by simp [map_sub, hab]))
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem overlapBranch_injective (negative : Bool) : Function.Injective (overlapBranch negative) := by
  have hi : Function.Injective
      ((overlapBranch negative).comp N13SpecialCurveOverlap.overlapEquiv.toRingHom) := by
    apply localization_hom_injective (Submonoid.powers N13SpecialCurveOverlap.xClass)
    intro a b hab
    apply affineBranch_injective negative
    change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO a)) =
      overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv (algebraMap R AO b)) at hab
    simpa only [N13SpecialCurveOverlap.overlapEquiv_apply,
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap,
      overlapBranch_affine] using hab
  intro a b hab
  apply N13SpecialCurveOverlap.overlapEquiv.symm.injective
  apply hi
  change overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm a)) =
    overlapBranch negative (N13SpecialCurveOverlap.overlapEquiv
      (N13SpecialCurveOverlap.overlapEquiv.symm b))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hab
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinity_t_ne_zero : N13SpecialInfinityChart.tClass ≠ 0 := by
  have hd : N13SpecialInfinityChart.curvePoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree N13SpecialInfinityChart.curvePoly_monic.ne_zero,
      N13SpecialInfinityChart.curvePoly_natDegree]
    norm_num
  change AdjoinRoot.of N13SpecialInfinityChart.curvePoly X ≠ 0
  simpa only [map_zero] using
    (AdjoinRoot.of.injective_of_degree_ne_zero hd).ne (Polynomial.X_ne_zero : (X : K[X]) ≠ 0)
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinityBranch_injective (negative : Bool) : Function.Injective (infinityBranch negative) := by
  intro a b hab
  apply IsLocalization.injective O
    (powers_le_nonZeroDivisors_of_noZeroDivisors infinity_t_ne_zero)
  apply overlapBranch_injective negative
  simpa only [overlapBranch_infinity] using congrArg includeSeries hab
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialBranchFaithfulness
noncomputable section
open Polynomial N13SpecialLaurentBranches N13SpecialOverlapBranches
open scoped nonZeroDivisors
theorem infinityBranch_ne_zero (negative : Bool) (b : B) (hb : b ≠ 0) : infinityBranch negative b ≠ 0 := by
  simpa only [map_zero] using (infinityBranch_injective negative).ne hb
end
end MazurProof.N13SpecialBranchFaithfulness
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityBranch_t (negative : Bool) :
    infinityBranch negative N13SpecialInfinityChart.tClass = PowerSeries.X := by
  cases negative <;> simp [infinityBranch]
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityBranch_constant (negative : Bool) (a : K) :
    infinityBranch negative (algebraMap K[X] B (C a)) = PowerSeries.C a := by
  cases negative
  · change N13SpecialInfinityBranchJets.plus
      (N13IntegralInfinityReduction.specialBaseClass (C a)) = _
    rw [N13SpecialInfinityBranchJets.plus_base]
    simp [N13SpecialInfinityBranchJets.beta]
  · change N13SpecialInfinityBranchJets.minus
      (N13IntegralInfinityReduction.specialBaseClass (C a)) = _
    rw [N13SpecialInfinityBranchJets.minus_base]
    simp [N13SpecialInfinityBranchJets.beta]
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
private theorem branch_finite_point (negative : Bool) (v : K) :
    Ideal.map (infinityBranch negative) (infinityPointIdeal 1 v) = ⊤ := by
  let I := Ideal.map (infinityBranch negative) (infinityPointIdeal 1 v)
  have hm : PowerSeries.X - PowerSeries.C (1 : K) ∈ I := by
    have hmem : N13SpecialInfinityChart.tClass - algebraMap K[X] B (C (1 : K)) ∈
        infinityPointIdeal 1 v := Ideal.subset_span (by simp)
    simpa only [map_sub, infinityBranch_t, infinityBranch_constant] using
      Ideal.mem_map_of_mem (infinityBranch negative) hmem
  have hu : IsUnit (PowerSeries.X - PowerSeries.C (1 : K) : P) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using (isUnit_neg_one : IsUnit (-1 : K))
  exact I.eq_top_of_isUnit_mem hm hu
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem point_branch_ideal (negative : Bool) (P : CurvePoint) :
    Ideal.map (infinityBranch negative) (point P).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ pointOrder negative P} : Set N13SpecialLaurentBranches.P) := by
  cases P with
  | inl P =>
    change Ideal.map (infinityBranch negative) (point (Sum.inl P)).infinityIdeal = _
    simp only [pointOrder, pow_zero, Ideal.span_singleton_one]
    simp only [point]
    split
    · simp [affineZeroPoint, Ideal.map_top]
    · exact branch_finite_point negative P.1.2
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv
    · cases negative
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.plus_positive_point
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.minus_positive_point
    · cases negative
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.plus_negative_point
      · simpa [infinityBranch, point, infinityPoint, pointOrder, hv] using
          N13SpecialInfinityBranchJets.minus_negative_point
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
theorem point_degree_balance (P : CurvePoint) :
    (pointPolynomial P).natDegree + pointOrder false P + pointOrder true P = 1 := by
  cases P with
  | inl P => simp [pointPolynomial, pointOrder]
  | inr P =>
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one P.1 (ZMod.pow_card P.1) with hv | hv <;>
      simp [pointPolynomial, pointOrder, hv]
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
theorem divisor_branch_ideal (negative : Bool) (D : EffectiveDivisorTwo) :
    Ideal.map (infinityBranch negative) (ofDivisor D).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ divisorOrder negative D} : Set N13SpecialLaurentBranches.P) := by
  refine Sym2.inductionOn D ?_
  intro P Q
  change Ideal.map (infinityBranch negative) ((point P).infinityIdeal * (point Q).infinityIdeal) = _
  rw [Ideal.map_mul, point_branch_ideal, point_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
theorem divisor_degree_balance (D : EffectiveDivisorTwo) :
    (divisorPolynomial D).natDegree + divisorOrder false D + divisorOrder true D = 2 := by
  refine Sym2.inductionOn D ?_
  intro P Q
  rw [divisorPolynomial_mk, Polynomial.natDegree_mul
    (pointPolynomial_monic P).ne_zero (pointPolynomial_monic Q).ne_zero,
    divisorOrder_mk, divisorOrder_mk]
  have hp := point_degree_balance P
  have hq := point_degree_balance Q
  omega
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
def tensorOrder (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  divisorOrder negative D + divisorOrder negative E
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
theorem tensor_branch_ideal (negative : Bool) (D E : EffectiveDivisorTwo) :
    Ideal.map (infinityBranch negative) (tensor (ofDivisor D) (ofDivisor E)).infinityIdeal =
      Ideal.span ({PowerSeries.X ^ tensorOrder negative D E} : Set N13SpecialLaurentBranches.P) := by
  change Ideal.map (infinityBranch negative) ((ofDivisor D).infinityIdeal * (ofDivisor E).infinityIdeal) = _
  rw [Ideal.map_mul, divisor_branch_ideal, divisor_branch_ideal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
  rfl
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
theorem tensor_degree_balance (D E : EffectiveDivisorTwo) :
    (tensorPolynomial D E).natDegree + tensorOrder false D E + tensorOrder true D E = 4 := by
  rw [tensorPolynomial, Polynomial.natDegree_mul
    (divisorPolynomial_monic D).ne_zero (divisorPolynomial_monic E).ne_zero]
  have hd := divisor_degree_balance D
  have he := divisor_degree_balance E
  unfold tensorOrder
  omega
end
end MazurProof.N13SpecialDivisorBranchOrders
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem include_X : includeSeries (PowerSeries.X : N13SpecialLaurentBranches.P) = t :=
  HahnSeries.ofPowerSeries_X
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem include_unit_order (u : N13SpecialLaurentBranches.Pˣ) :
    (includeSeries (u : N13SpecialLaurentBranches.P)).order = 0 := by
  have hp : includeSeries (u : N13SpecialLaurentBranches.P) * includeSeries (↑(u⁻¹) : N13SpecialLaurentBranches.P) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ho := HahnSeries.order_mul (u.isUnit.map includeSeries).ne_zero ((u⁻¹).isUnit.map includeSeries).ne_zero
  rw [hp, HahnSeries.order_one] at ho
  have hu := include_order_nonnegative (u : N13SpecialLaurentBranches.P)
  have hv := include_order_nonnegative (↑(u⁻¹) : N13SpecialLaurentBranches.P)
  omega
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem t_pow_order (n : ℕ) : (t ^ n).order = (n : ℤ) := by
  rw [HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter]
  simp
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
theorem order_balance_of_principal_power_eq
    (f g : N13SpecialLaurentBranches.P) (hf : f ≠ 0) (hg : g ≠ 0) (n m : ℕ)
    (h : Ideal.span ({f} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ n} : Set N13SpecialLaurentBranches.P) =
      Ideal.span ({g} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ m} : Set N13SpecialLaurentBranches.P)) :
    (includeSeries f).order + (n : ℤ) = (includeSeries g).order + (m : ℤ) := by
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have he := congrArg includeSeries hu
  simp only [map_mul, map_pow, include_X] at he
  have hf' : includeSeries f ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hf
  have hg' : includeSeries g ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hg
  have ho := congrArg HahnSeries.order he
  rw [HahnSeries.order_mul (mul_ne_zero hf' (pow_ne_zero n t_ne_zero)) (u.isUnit.map includeSeries).ne_zero,
    HahnSeries.order_mul hf' (pow_ne_zero n t_ne_zero),
    HahnSeries.order_mul hg' (pow_ne_zero m t_ne_zero),
    include_unit_order, t_pow_order, t_pow_order, add_zero] at ho
  exact ho
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
theorem comparison_infinity_order_balance
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    (includeSeries (infinityBranch negative h.iNum)).order + (tensorOrder negative D E : ℤ) =
      (includeSeries (infinityBranch negative h.iDen)).order + (tensorOrder negative F H : ℤ) := by
  have he := congrArg (Ideal.map (infinityBranch negative)) h.infinity_eq
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, tensor_branch_ideal] at he
  exact order_balance_of_principal_power_eq _ _
    (infinityBranch_ne_zero negative _ h.iNum_ne) (infinityBranch_ne_zero negative _ h.iDen_ne) _ _ he
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem affineBranch_ne_zero (negative : Bool) (z : R) (hz : z ≠ 0) : affineBranch negative z ≠ 0 := by
  simpa only [map_zero] using (affineBranch_injective negative).ne hz
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
private theorem affineBranch_xClass (negative : Bool) (p : K[X]) :
    affineBranch negative (N13GoodCoordinateRingTwo.xClass p) = base p := by
  cases negative <;> simp [affineBranch]
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
/-- The previously missing two-infinity bounds for the ACTUAL cleared
numerator extracted from a special comparison. -/
theorem cleared_numerator_pole_bound
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (-4 : ℤ) ≤ (affineBranch negative z).order := by
  have ha := affineBranch_ne_zero negative _ h.aNum_ne
  have hb := affineBranch_ne_zero negative _ h.aDen_ne
  have hc : includeSeries (infinityBranch negative h.iNum) ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr
      (infinityBranch_ne_zero negative _ h.iNum_ne)
  have hd : includeSeries (infinityBranch negative h.iDen) ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr
      (infinityBranch_ne_zero negative _ h.iDen_ne)
  have he := congrArg HahnSeries.order (cross_relation negative _ _ _ _ h.overlap_eq)
  rw [HahnSeries.order_mul ha hd, HahnSeries.order_mul hb hc] at he
  have hi := comparison_infinity_order_balance negative D E F H h
  have hn := congrArg (affineBranch negative) hcross
  simp only [map_mul, affineBranch_xClass] at hn
  have hq := (tensorPolynomial_monic D E).ne_zero
  have ho := congrArg HahnSeries.order hn
  rw [HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hq),
    HahnSeries.order_mul hb (affineBranch_ne_zero negative z hz),
    N13BranchNorm.evalPoly_order K _ hq] at ho
  have hdegree : (tensorPolynomial D E).natDegree + tensorOrder negative D E ≤ 4 := by
    have hh := tensor_degree_balance D E
    cases negative <;> omega
  have hr : 0 ≤ (tensorOrder negative F H : ℤ) := Nat.cast_nonneg _
  omega
end
end MazurProof.N13SpecialSmallNumerator
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
namespace MazurProof.N13SpecialSmallNumerator
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness
/-- Reduction to the genuine 32-by-4 polynomial search space over F2.
The small numerator retains the input fraction and has supported norm. -/
theorem exists_small_supported_numerator
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ p q : K[X], ∃ i j : ℕ,
      p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 ∧ i + j ≤ 16 ∧
      N13SpecialAffineNorm.linear p q ≠ 0 ∧
      h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) =
        h.aDen * N13SpecialAffineNorm.linear p q ∧
      N13SpecialAffineNorm.normPolynomial p q ≠ 0 ∧
      N13SpecialAffineNorm.normPolynomial p q ∣ X ^ i * (X - 1) ^ j := by
  obtain ⟨z, w, i, j, hij, hz, _, hcross, _, _, hnorm⟩ :=
    N13SpecialAffineNorm.exists_factor_pair_with_supported_norm D E F H h
  have hrepr : N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) = z :=
    N13GoodCoordinateRingTwo.recompose z
  have hp := cleared_numerator_pole_bound false D E F H h z hz hcross
  have hm := cleared_numerator_pole_bound true D E F H h z hz hcross
  change (-4 : ℤ) ≤ (plus z).order at hp
  change (-4 : ℤ) ≤ (minus z).order at hm
  have hbounds := degree_four_polynomial_bounds
    (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z)
    (by rw [hrepr]; exact hp) (by rw [hrepr]; exact hm)
  refine ⟨_, _, i, j, hbounds.1, hbounds.2, hij, ?_, ?_, ?_, hnorm⟩
  · rw [hrepr]; exact hz
  · rw [hrepr]; exact hcross
  · exact N13SpecialAffineNorm.norm_ne_zero z hz
end
end MazurProof.N13SpecialSmallNumerator
end
end
end
end
end
end
end
end

open Polynomial
theorem solution
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    ∃ p q : MazurProof.N13SpecialDivisorCharts.K[X], ∃ i j : ℕ,
      p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 ∧ i + j ≤ 16 ∧
      MazurProof.N13SpecialAffineNorm.linear p q ≠ 0 ∧
      h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) =
        h.aDen * MazurProof.N13SpecialAffineNorm.linear p q ∧
      MazurProof.N13SpecialAffineNorm.normPolynomial p q ≠ 0 ∧
      MazurProof.N13SpecialAffineNorm.normPolynomial p q ∣ X ^ i * (X - 1) ^ j := by
  exact MazurProof.N13SpecialSmallNumerator.exists_small_supported_numerator D E F H h
