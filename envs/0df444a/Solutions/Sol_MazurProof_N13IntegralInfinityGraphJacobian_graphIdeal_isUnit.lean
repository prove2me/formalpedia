-- Prove2me | solution 1 for MazurProof.N13IntegralInfinityGraphJacobian.graphIdeal_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:53:15.59181+00:00
-- url     : https://prove2.me/submissions/4b5b1d0a-a4cd-4969-9bbd-4fd0b61bd67c

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_infinityOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Definitions.Def_MazurN13_L4


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityGraphJacobian
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralInfinityGraphJacobian.instFactPrimeOfNatNat_fLT

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.GraphJacobianDualFrame
noncomputable section
variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
/-- A graph factorization and a global Jacobian Bézout identity produce an
explicit dual frame, hence an invertible graph fractional ideal. -/
theorem graphJacobian_isUnit
    (U G Gbar W Fy Fx Ux Wx Vx hx a b : A)
    (hU : U ≠ 0)
    (hGGbar : G * Gbar = -(U * W))
    (hFy : Fy = G + Gbar)
    (hFx :
      Fx =
        Ux * W + U * Wx - Vx * Gbar +
          (hx + Vx) * G)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    dsimp only [I]
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    intro hmapU0
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hGGbarK :
      algebraMap A K G * algebraMap A K Gbar =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGGbar
  let z : K :=
    -algebraMap A K Gbar / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K Gbar := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K Gbar *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K Gbar) /
            algebraMap A K U := by
              ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by
              rw [hGGbarK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change
      y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * Gbar + d * W, ?_⟩
    calc
      algebraMap A K (-c * Gbar + d * W) =
          algebraMap A K c *
              (-algebraMap A K Gbar) +
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
      _ = z * algebraMap A K yA := by
            rw [hcd]
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
  let tU : K :=
    algebraMap A K a *
        (algebraMap A K Wx +
          algebraMap A K Vx * z) -
      algebraMap A K b * z
  let tG : K :=
    algebraMap A K a *
        (algebraMap A K Ux * z +
          algebraMap A K hx +
          algebraMap A K Vx) +
      algebraMap A K b
  have htU : tU ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Wx +
            algebraMap A K Vx * z ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (hIntegral Wx) (hScalarZ Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
        hscaled (hScalarZ b))
  have htG : tG ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Ux * z +
            algebraMap A K hx +
            algebraMap A K Vx ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem
          (hScalarZ Ux) (hIntegral hx))
        (hIntegral Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        hscaled (hIntegral b))
  have hGbarK :
      algebraMap A K Gbar =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K Ux * algebraMap A K W +
          algebraMap A K U * algebraMap A K Wx -
          algebraMap A K Vx *
            algebraMap A K Gbar +
          (algebraMap A K hx +
              algebraMap A K Vx) *
            algebraMap A K G := by
    simpa only [map_add, map_sub, map_mul] using
      congrArg (algebraMap A K) hFx
  have hFx_decomp :
      algebraMap A K Fx =
        algebraMap A K U *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) +
          algebraMap A K G *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) := by
    calc
      algebraMap A K Fx =
          algebraMap A K Ux *
              algebraMap A K W +
            algebraMap A K U *
              algebraMap A K Wx -
            algebraMap A K Vx *
              algebraMap A K Gbar +
            (algebraMap A K hx +
                algebraMap A K Vx) *
              algebraMap A K G :=
        hFxK
      _ =
          algebraMap A K U *
              (algebraMap A K Wx +
                algebraMap A K Vx * z) +
            algebraMap A K G *
              (algebraMap A K Ux * z +
                algebraMap A K hx +
                algebraMap A K Vx) := by
              rw [hWK, hGbarK]
              ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K G +
          algebraMap A K Gbar := by
    simpa only [map_add] using
      congrArg (algebraMap A K) hFy
  have hFy_decomp :
      algebraMap A K Fy =
        algebraMap A K U * (-z) +
          algebraMap A K G := by
    calc
      algebraMap A K Fy =
          algebraMap A K G +
            algebraMap A K Gbar :=
        hFyK
      _ =
          algebraMap A K U * (-z) +
            algebraMap A K G := by
              rw [hGbarK]
              ring
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
              (algebraMap A K U *
                  (algebraMap A K Wx +
                    algebraMap A K Vx * z) +
                algebraMap A K G *
                  (algebraMap A K Ux * z +
                    algebraMap A K hx +
                    algebraMap A K Vx)) +
            algebraMap A K b *
              (algebraMap A K U * (-z) +
                algebraMap A K G) := by
                dsimp only [tU, tG]
                ring
      _ =
          algebraMap A K a *
              algebraMap A K Fx +
            algebraMap A K b *
              algebraMap A K Fy := by
                rw [← hFx_decomp, ← hFy_decomp]
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
  have hunitI : IsUnit I :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      hmul_eq
  simpa only [I, M] using hunitI
end
end MazurProof.GraphJacobianDualFrame
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
/-- The product of the two raw graph functions is the negative substituted
curve equation. -/
theorem ySubClass_mul_conjugateV_raw
    (xClass : R[X] →+* A) (yClass : A) (h rhs v : R[X])
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass v *
        ySubClass xClass yClass (conjugateV h v) =
      -xClass (v ^ 2 + h * v - rhs) := by
  calc
    ySubClass xClass yClass v *
          ySubClass xClass yClass (conjugateV h v) =
        yClass ^ 2 + xClass h * yClass -
          (xClass v ^ 2 + xClass h * xClass v) := by
      simp only [ySubClass, conjugateV, map_neg, map_sub]
      ring
    _ = xClass rhs - xClass (v ^ 2 + h * v) := by
      rw [hy, map_add, map_mul, map_pow]
    _ = -xClass (v ^ 2 + h * v - rhs) := by
      rw [map_sub]
      ring
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
theorem ySubClass_mul_conjugate
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass D.v *
        ySubClass xClass yClass (conjugateV h D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass xClass yClass D.v *
          ySubClass xClass yClass (conjugateV h D.v) =
        -xClass (D.v ^ 2 + h * D.v - rhs) :=
      ySubClass_mul_conjugateV_raw xClass yClass h rhs D.v hy
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [map_mul]
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
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem derivative_graphData_curve_eq
    (D : GraphData) :
    (C (2 : R₂) * D.v +
          N13IntegralInfinityChart.hBase) *
          derivative D.v +
        derivative N13IntegralInfinityChart.hBase * D.v -
        derivative N13IntegralInfinityChart.rhsBase =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h
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
private theorem jacobianV_eq_graphData
    (D : GraphData) :
    jacobianV =
      GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v +
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV
              N13IntegralInfinityChart.hBase D.v) := by
  simp only [jacobianV,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    map_neg, map_sub]
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
private theorem jacobianT_eq_graphData
    (D : GraphData) :
    jacobianT =
      xClassHom (derivative D.u) * xClassHom D.w +
        xClassHom D.u * xClassHom (derivative D.w) -
        xClassHom (derivative D.v) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV
                N13IntegralInfinityChart.hBase D.v) +
        (xClassHom
              (derivative N13IntegralInfinityChart.hBase) +
            xClassHom (derivative D.v)) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v := by
  have h :=
    congrArg xClassHom
      (derivative_graphData_curve_eq D)
  have htwo :
      xClassHom (C (2 : R₂)) =
        (2 : InfinityCurve) := by
    exact map_natCast xClassHom 2
  simp only [jacobianT,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    map_add, map_sub, map_neg, map_mul] at h ⊢
  rw [htwo] at h
  linear_combination h
end
end MazurProof.N13IntegralInfinityGraphJacobian
end
end
end

attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem solution (D : GraphData) (hu : D.u ≠ 0) : IsUnit ((GeneralizedGraphIdealCore.graphIdeal xClassHom yClass D.u D.v : Ideal InfinityCurve) : InfinityFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    exists_jacobian_bezout
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClassHom D.u)
      (G :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v)
      (Gbar :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV
              N13IntegralInfinityChart.hBase D.v))
      (W := xClassHom D.w)
      (Fy := jacobianV)
      (Fx := jacobianT)
      (Ux := xClassHom (derivative D.u))
      (Wx := xClassHom (derivative D.w))
      (Vx := xClassHom (derivative D.v))
      (hx :=
        xClassHom
          (derivative N13IntegralInfinityChart.hBase))
      (a := a) (b := b)
  · change
      N13IntegralInfinityPointSpread.xClassHom D.u ≠ 0
    intro hzero
    apply hu
    apply N13IntegralInfinityPointSpread.xClassHom_injective
    simpa only [map_zero] using hzero
  · exact
      GeneralizedGraphIdealCore.ySubClass_mul_conjugate
        xClassHom yClass
        N13IntegralInfinityChart.hBase
        N13IntegralInfinityChart.rhsBase
        D
        N13IntegralInfinityPointSpread.yClass_relation
  · exact jacobianV_eq_graphData D
  · exact jacobianT_eq_graphData D
  · exact hBez
