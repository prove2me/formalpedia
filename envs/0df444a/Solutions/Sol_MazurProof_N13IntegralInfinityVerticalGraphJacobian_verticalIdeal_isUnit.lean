-- Prove2me | solution 1 for MazurProof.N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:56:01.921474+00:00
-- url     : https://prove2.me/submissions/bb954ded-4367-4832-b8f5-dcc22584b5dd

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_infinityOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityVerticalGraphJacobian
open Polynomial
open scoped nonZeroDivisors
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphJacobian.instFactPrimeOfNatNat_fLT

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.GraphJacobianDecompositionFrame
noncomputable section
variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
theorem graphJacobian_isUnit_of_decompositions
    (U G H W Fx Fy
      αx βx γx δx αy βy γy δy a b : A)
    (hU : U ≠ 0)
    (hGH : G * H = -(U * W))
    (hFx :
      Fx = U * αx + G * βx + H * γx + W * δx)
    (hFy :
      Fy = U * αy + G * βy + H * γy + W * δy)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective A K).ne hU
  have hGHK :
      algebraMap A K G * algebraMap A K H =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGH
  let z : K :=
    -algebraMap A K H / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K H := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K H *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K H) /
            algebraMap A K U := by ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by rw [hGHK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * H + d * W, ?_⟩
    calc
      algebraMap A K (-c * H + d * W) =
          algebraMap A K c *
              (-algebraMap A K H) +
            algebraMap A K d *
              algebraMap A K W := by
                simp only [map_add, map_mul, map_neg]
                ring
      _ =
          algebraMap A K c *
              (z * algebraMap A K U) +
            algebraMap A K d *
              (z * algebraMap A K G) := by
                rw [← hzU, ← hzG]
      _ =
          z * algebraMap A K
            (c * U + d * G) := by
              simp only [map_add, map_mul]
              ring
      _ = z * algebraMap A K yA := by rw [hcd]
  have hone_inv : (1 : K) ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    simpa only [one_mul] using hI_le_one hy
  have hIntegral (r : A) :
      algebraMap A K r ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hone_inv)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, mul_one] using hr
  have hScalarZ (r : A) :
      algebraMap A K r * z ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hz_mem)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def] using hr
  let ux : K :=
    algebraMap A K αx - algebraMap A K γx * z
  let gx : K :=
    algebraMap A K βx + algebraMap A K δx * z
  let uy : K :=
    algebraMap A K αy - algebraMap A K γy * z
  let gy : K :=
    algebraMap A K βy + algebraMap A K δy * z
  have hux : ux ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αx) (hScalarZ γx))
  have hgx : gx ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βx) (hScalarZ δx))
  have huy : uy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αy) (hScalarZ γy))
  have hgy : gy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βy) (hScalarZ δy))
  have hHK :
      algebraMap A K H =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K U * ux +
          algebraMap A K G * gx := by
    rw [hFx]
    simp only [map_add, map_mul, ux, gx]
    rw [hHK, hWK]
    ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K U * uy +
          algebraMap A K G * gy := by
    rw [hFy]
    simp only [map_add, map_mul, uy, gy]
    rw [hHK, hWK]
    ring
  let tU : K :=
    algebraMap A K a * ux +
      algebraMap A K b * uy
  let tG : K :=
    algebraMap A K a * gx +
      algebraMap A K b * gy
  have htU : tU ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hux)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b huy))
  have htG : tG ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hgx)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b hgy))
  have hBezK :
      algebraMap A K a *
            algebraMap A K Fx +
          algebraMap A K b *
            algebraMap A K Fy = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (algebraMap A K) hBez
  have hframe :
      algebraMap A K U * tU +
          algebraMap A K G * tG = 1 := by
    calc
      algebraMap A K U * tU +
            algebraMap A K G * tG =
          algebraMap A K a *
              (algebraMap A K U * ux +
                algebraMap A K G * gx) +
            algebraMap A K b *
              (algebraMap A K U * uy +
                algebraMap A K G * gy) := by
          dsimp only [tU, tG]
          ring
      _ =
          algebraMap A K a * algebraMap A K Fx +
            algebraMap A K b * algebraMap A K Fy := by
        rw [← hFxK, ← hFyK]
      _ = 1 := hBezK
  have hmul_le : I * I⁻¹ ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hxy :=
      (FractionalIdeal.mem_inv_iff hI_ne).mp
        hy x hx
    simpa only [mul_comm] using hxy
  have hone_le : 1 ≤ I * I⁻¹ := by
    rw [FractionalIdeal.one_le, ← hframe]
    simpa only [FractionalIdeal.mem_coe] using
      (((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (FractionalIdeal.mul_mem_mul hU_I htU)
          (FractionalIdeal.mul_mem_mul hG_I htG))
  have hmul_eq : I * I⁻¹ = 1 :=
    le_antisymm hmul_le hone_le
  exact
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp hmul_eq
end
end MazurProof.GraphJacobianDecompositionFrame
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
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_hBase_explicit :
    derivative N13IntegralInfinityChart.hBase =
      (3 : R₂[X]) * X ^ 2 + 2 * X := by
  rw [show (3 : R₂[X]) = C (3 : R₂) by
      exact (map_natCast C 3).symm,
    show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.hBase,
    derivative_add, derivative_pow]
  ring
end
end MazurProof.N13IntegralInfinityGraphJacobian
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
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_rhsBase_explicit :
    derivative N13IntegralInfinityChart.rhsBase =
      1 + 2 * X := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.rhsBase,
    derivative_add, derivative_pow]
end
end MazurProof.N13IntegralInfinityGraphJacobian
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
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The infinity-chart Jacobian certificate.  It is the reciprocal-chart
counterpart of the affine certificate with value `13`. -/
theorem scaled_jacobian_bezout :
    bezoutA * jacobianT + bezoutB * jacobianV =
      (117 : InfinityCurve) := by
  have hcurve :=
    N13IntegralInfinityPointSpread.yClass_relation
  have hX :
      xClassHom X = N13IntegralInfinityChart.tClass :=
    N13IntegralInfinityPointSpread.xClassHom_X
  have h2 :
      xClassHom (2 : Base) = (2 : InfinityCurve) :=
    map_natCast xClassHom 2
  have h3 :
      xClassHom (3 : Base) = (3 : InfinityCurve) :=
    map_natCast xClassHom 3
  have hC2 :
      xClassHom (C (2 : R₂)) = (2 : InfinityCurve) := by
    rw [show C (2 : R₂) = (2 : Base) by
      exact map_natCast C 2]
    exact h2
  have hC3 :
      xClassHom (C (3 : R₂)) = (3 : InfinityCurve) := by
    rw [show C (3 : R₂) = (3 : Base) by
      exact map_natCast C 3]
    exact h3
  simp [jacobianT, jacobianV,
    derivative_hBase_explicit,
    derivative_rhsBase_explicit,
    bezoutA, bezoutB,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    yClass, hX, hC2, hC3] at hcurve ⊢
  linear_combination
    (1350 * N13IntegralInfinityChart.tClass ^ 4 +
      1872 * N13IntegralInfinityChart.tClass ^ 3 +
      243 * N13IntegralInfinityChart.tClass ^ 2 +
      1134 * N13IntegralInfinityChart.tClass + 2466) * hcurve
end
end MazurProof.N13IntegralInfinityGraphJacobian
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
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem oneHundredSeventeen_isUnit :
    IsUnit (117 : InfinityCurve) := by
  have h : IsUnit (117 : R₂) := by
    rw [PadicInt.isUnit_iff]
    exact
      PadicInt.norm_natCast_eq_one_iff.mpr
        (by norm_num)
  convert h.map
    ((algebraMap Base InfinityCurve).comp
      (Polynomial.C : R₂ →+* Base)) using 1
  exact
    (map_natCast
      ((algebraMap Base InfinityCurve).comp
        (Polynomial.C : R₂ →+* Base)) 117).symm
end
end MazurProof.N13IntegralInfinityGraphJacobian
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
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The two relative Jacobian rows generate one globally on the ordinary
infinity chart. -/
theorem exists_jacobian_bezout :
    ∃ a b : InfinityCurve,
      a * jacobianT + b * jacobianV = 1 := by
  let u : InfinityCurveˣ :=
    oneHundredSeventeen_isUnit.unit
  refine
    ⟨(u⁻¹ : InfinityCurveˣ) * bezoutA,
      (u⁻¹ : InfinityCurveˣ) * bezoutB, ?_⟩
  calc
    (((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
            bezoutA) * jacobianT +
          (((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
            bezoutB) * jacobianV =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
          (bezoutA * jacobianT +
            bezoutB * jacobianV) := by ring
    _ =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) * 117 := by
      rw [scaled_jacobian_bezout]
    _ =
        ((u⁻¹ : InfinityCurveˣ) : InfinityCurve) *
          (u : InfinityCurve) := by
      rw [oneHundredSeventeen_isUnit.unit_spec]
    _ = 1 := by simp
end
end MazurProof.N13IntegralInfinityGraphJacobian
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
@[simp] theorem integralCoeff0_baseClass (p : IntegralBase) :
    integralCoeff0 (integralBaseClass p) = p := by
  change
    (C p %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [integral_curve_degree]
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem integralCoeff0_vClass :
    integralCoeff0 N13IntegralInfinityChart.vClass = 0 := by
  change
    (X %ₘ N13IntegralInfinityChart.infinityCurvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff
      N13IntegralInfinityChart.infinityCurvePoly_monic).mpr]
  · simp
  · rw [degree_X, integral_curve_degree]
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
@[simp] theorem integralCoeff0_baseClass_mul_vClass
    (p : IntegralBase) :
    integralCoeff0
        (integralBaseClass p *
          N13IntegralInfinityChart.vClass) = 0 := by
  change integralCoeff0
    ((algebraMap IntegralBase IntegralRing p) *
      N13IntegralInfinityChart.vClass) = 0
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
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem xClassHom_X :
    xClassHom X = N13IntegralInfinityChart.tClass := by
  rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem verticalCurve_eval
    (E : VerticalGraph) :
    yClass ^ 2 +
          (1 + L E ^ 2 + L E ^ 3) * yClass -
        (L E + L E ^ 2) =
      U E * W E := by
  have h :=
    congrArg (aeval yClass) E.curve_eq
  simpa [verticalCurve, VerticalGraph.s, L, U, W,
    N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase,
    aeval_comp] using h
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem curve_eval :
    yClass ^ 2 +
          (1 + N13IntegralInfinityChart.tClass ^ 2 +
              N13IntegralInfinityChart.tClass ^ 3) * yClass -
        (N13IntegralInfinityChart.tClass +
          N13IntegralInfinityChart.tClass ^ 2) =
      0 := by
  have h :
      yClass ^ 2 +
          xClassHom N13IntegralInfinityChart.hBase * yClass =
        xClassHom N13IntegralInfinityChart.rhsBase := by
    exact N13IntegralInfinityPointSpread.yClass_relation
  simp only [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase, map_add, map_pow, map_one,
    xClassHom_X] at h
  exact sub_eq_zero.mpr h
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Exact complementary factorization in the infinity coordinate ring. -/
theorem G_mul_Gbar
    (E : VerticalGraph) :
    G E * Gbar E = -(U E * W E) := by
  have ht := curve_eval
  have hL := verticalCurve_eval E
  dsimp only [G, Gbar]
  linear_combination ht - hL
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_hBase :
    derivative N13IntegralInfinityChart.hBase =
      2 * X + 3 * X ^ 2 := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm,
    show (3 : R₂[X]) = C (3 : R₂) by
      exact (map_natCast C 3).symm]
  simp [N13IntegralInfinityChart.hBase,
    derivative_add, derivative_pow]
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_rhsBase :
    derivative N13IntegralInfinityChart.rhsBase =
      1 + 2 * X := by
  rw [show (2 : R₂[X]) = C (2 : R₂) by
      exact (map_natCast C 2).symm]
  simp [N13IntegralInfinityChart.rhsBase,
    derivative_add, derivative_pow]
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem jacobianT_explicit :
    jacobianT =
      yClass *
          (2 * N13IntegralInfinityChart.tClass +
            3 * N13IntegralInfinityChart.tClass ^ 2) -
        (1 + 2 * N13IntegralInfinityChart.tClass) := by
  have h2 :
      xClassHom (2 : R₂[X]) = (2 : InfinityCurve) :=
    map_natCast xClassHom 2
  have h3 :
      xClassHom (3 : R₂[X]) = (3 : InfinityCurve) :=
    map_natCast xClassHom 3
  rw [jacobianT, derivative_hBase, derivative_rhsBase]
  simp only [map_add, map_mul, map_pow, map_one]
  rw [h2, h3, xClassHom_X]
  ring
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem jacobianV_explicit :
    jacobianV =
      2 * yClass +
        1 + N13IntegralInfinityChart.tClass ^ 2 +
          N13IntegralInfinityChart.tClass ^ 3 := by
  simp only [jacobianV, N13IntegralInfinityChart.hBase,
    map_add, map_pow, map_one, xClassHom_X]
  ring
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem jacobianT_decomposition
    (E : VerticalGraph) :
    jacobianT = G E * GbarT E + Gbar E := by
  rw [jacobianT_explicit]
  simp only [G, GbarT, Gbar]
  ring
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_verticalCurve
    (E : VerticalGraph) :
    algebraMap R₂ InfinityCurve E.c *
          (yClass * (2 * L E + 3 * L E ^ 2) -
            (1 + 2 * L E)) +
        (2 * yClass + 1 + L E ^ 2 + L E ^ 3) =
      U E * Wv E + W E * Uv E := by
  have hder :=
    congrArg derivative E.curve_eq
  have h :=
    congrArg (aeval yClass) hder
  simp only [verticalCurve, derivative_sub, derivative_add,
    derivative_mul, derivative_pow, derivative_X,
    derivative_comp, derivative_C, zero_add, zero_mul,
    map_sub, map_add, map_mul, map_pow, map_one,
    aeval_X, aeval_comp, Polynomial.aeval_C] at h
  rw [derivative_hBase, derivative_rhsBase] at h
  simp only [map_add, map_mul, map_pow, map_one, aeval_X] at h
  norm_num only [map_ofNat] at h
  change
    algebraMap R₂ InfinityCurve E.c *
          (yClass * (2 * L E + 3 * L E ^ 2) -
            (1 + 2 * L E)) +
        (2 * yClass + 1 + L E ^ 2 + L E ^ 3) =
      U E * Wv E + W E * Uv E
  dsimp only [L, U, W, Uv, Wv, VerticalGraph.s]
  simp [N13IntegralInfinityChart.hBase,
    N13IntegralInfinityChart.rhsBase] at h
  simp only [map_add, map_mul, Polynomial.aeval_C, aeval_X]
  linear_combination h
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem jacobianV_decomposition
    (E : VerticalGraph) :
    jacobianV =
      G E * GbarV E +
        U E * Wv E +
        W E * Uv E +
        Gbar E * (-algebraMap R₂ InfinityCurve E.c) := by
  have hder := derivative_verticalCurve E
  rw [jacobianV_explicit]
  dsimp only [G, GbarV, Gbar]
  linear_combination hder
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem algebraMap_eq_baseClass_C
    (r : R₂) :
    algebraMap R₂ InfinityCurve r =
      N13IntegralInfinityReduction.integralBaseClass (C r) := by
  rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphJacobian
noncomputable section
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem G_ne_zero
    (E : VerticalGraph) :
    G E ≠ 0 := by
  intro hzero
  have hcoeff :=
    congrArg N13IntegralInfinityReduction.integralCoeff0 hzero
  simp only [G, L, VerticalGraph.s, map_sub, map_add, map_mul,
    Polynomial.aeval_C, aeval_X, map_zero] at hcoeff
  rw [algebraMap_eq_baseClass_C E.a,
    algebraMap_eq_baseClass_C E.c] at hcoeff
  rw [show
      N13IntegralInfinityChart.tClass =
        N13IntegralInfinityReduction.integralBaseClass X by rfl,
    show yClass = N13IntegralInfinityChart.vClass by rfl] at hcoeff
  simp only [map_sub, map_add,
    N13IntegralInfinityReduction.integralCoeff0_baseClass,
    N13IntegralInfinityReduction.integralCoeff0_baseClass_mul_vClass,
    sub_zero] at hcoeff
  have hcoeffOne :=
    congrArg (fun p : R₂[X] => p.coeff 1) hcoeff
  simpa using hcoeffOne
end
end MazurProof.N13IntegralInfinityVerticalGraphJacobian
end
end

attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem solution (E : MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph) : IsUnit ((E.ideal : Ideal MazurProof.N13IntegralInfinityVerticalGraphJacobian.InfinityCurve) : MazurProof.N13IntegralInfinityVerticalGraphJacobian.InfinityFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    MazurProof.N13IntegralInfinityGraphJacobian.exists_jacobian_bezout
  have hrelation :
      MazurProof.N13IntegralInfinityVerticalGraphJacobian.U E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.W E = -(MazurProof.N13IntegralInfinityVerticalGraphJacobian.G E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.Gbar E) := by
    have h := MazurProof.N13IntegralInfinityVerticalGraphJacobian.G_mul_Gbar E
    linear_combination h
  have hT :
      MazurProof.N13IntegralInfinityGraphJacobian.jacobianT =
        MazurProof.N13IntegralInfinityVerticalGraphJacobian.G E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.GbarT E +
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.U E * 0 + MazurProof.N13IntegralInfinityVerticalGraphJacobian.W E * 0 + MazurProof.N13IntegralInfinityVerticalGraphJacobian.Gbar E * 1 := by
    rw [MazurProof.N13IntegralInfinityVerticalGraphJacobian.jacobianT_decomposition]
    ring
  have hV :
      MazurProof.N13IntegralInfinityGraphJacobian.jacobianV =
        MazurProof.N13IntegralInfinityVerticalGraphJacobian.G E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.GbarV E +
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.U E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.Wv E +
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.W E * MazurProof.N13IntegralInfinityVerticalGraphJacobian.Uv E +
          MazurProof.N13IntegralInfinityVerticalGraphJacobian.Gbar E * (-algebraMap MazurProof.N13IntegralInfinityVerticalGraphJacobian.R₂ MazurProof.N13IntegralInfinityVerticalGraphJacobian.InfinityCurve E.c) :=
    MazurProof.N13IntegralInfinityVerticalGraphJacobian.jacobianV_decomposition E
  have hunit :=
    GraphJacobianDecompositionFrame.graphJacobian_isUnit_of_decompositions
      (K := MazurProof.N13IntegralInfinityVerticalGraphJacobian.FunctionField)
      (U := MazurProof.N13IntegralInfinityVerticalGraphJacobian.G E) (G := MazurProof.N13IntegralInfinityVerticalGraphJacobian.U E) (H := MazurProof.N13IntegralInfinityVerticalGraphJacobian.W E) (W := MazurProof.N13IntegralInfinityVerticalGraphJacobian.Gbar E)
      (Fx := MazurProof.N13IntegralInfinityGraphJacobian.jacobianT) (Fy := MazurProof.N13IntegralInfinityGraphJacobian.jacobianV)
      (αx := MazurProof.N13IntegralInfinityVerticalGraphJacobian.GbarT E) (βx := 0) (γx := 0) (δx := 1)
      (αy := MazurProof.N13IntegralInfinityVerticalGraphJacobian.GbarV E) (βy := MazurProof.N13IntegralInfinityVerticalGraphJacobian.Wv E)
      (γy := MazurProof.N13IntegralInfinityVerticalGraphJacobian.Uv E)
      (δy := -algebraMap MazurProof.N13IntegralInfinityVerticalGraphJacobian.R₂ MazurProof.N13IntegralInfinityVerticalGraphJacobian.InfinityCurve E.c)
      (a := a) (b := b)
      (MazurProof.N13IntegralInfinityVerticalGraphJacobian.G_ne_zero E) hrelation hT hV hBez
  have hideal :
      E.ideal = Ideal.span ({MazurProof.N13IntegralInfinityVerticalGraphJacobian.G E, MazurProof.N13IntegralInfinityVerticalGraphJacobian.U E} : Set MazurProof.N13IntegralInfinityVerticalGraphJacobian.InfinityCurve) := by
    apply congrArg Ideal.span
    ext z
    simp [VerticalGraph.ideal, MazurProof.N13IntegralInfinityVerticalGraphJacobian.U, MazurProof.N13IntegralInfinityVerticalGraphJacobian.G, MazurProof.N13IntegralInfinityVerticalGraphJacobian.L, or_comm]
  rw [hideal]
  exact hunit
