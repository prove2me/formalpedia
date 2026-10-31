-- Prove2me | solution 1 for HuangN13.N13FiniteAffineTwoChart.infinityClosure_isUnit_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:46:07.444486+00:00
-- url     : https://prove2.me/submissions/dcd27b5e-cd58-42e5-99cb-d812b4a600d6

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13IntegralFractionalHull_functionField_isFractionRing
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13ConcreteGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Evaluation at the integral affine `x` coordinate is the coordinate
embedding of the polynomial subring. -/
@[simp] theorem aeval_integralX (p : R₂[X]) :
    aeval N13CanonicalContractionQuotient.integralX p =
      N13GeneralizedMumfordIntegral.xClass (R := R₂) p := by
  change
    aeval
        (algebraMap R₂[X] IntegralRing X) p =
      algebraMap R₂[X] IntegralRing p
  simpa using
    aeval_algebraMap_apply IntegralRing
      (X : R₂[X]) p
end
end MazurProof.N13ConcreteGraphRecovery
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13ConcreteGraphRecovery
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Polynomial evaluation commutes with passage to any quotient of the
integral affine ring. -/
theorem quotient_aeval_integralX
    (I : Ideal IntegralRing) (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) p =
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) := by
  rw [← aeval_integralX]
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := IntegralRing) (T := R₂)
      (U := IntegralRing ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13CanonicalContractionQuotient.integralX).symm
end
end MazurProof.N13ConcreteGraphRecovery
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
open scoped nonZeroDivisors
namespace MazurProof.N13TraceGluing
noncomputable section
variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
/-- A generic-power certificate and a congruence-one trace certificate
force a fractional ideal to be a unit. -/
theorem isUnit_of_genericPower_and_modUniformizerTrace
    (M : FractionalIdeal A⁰ K)
    {f : A}
    (hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ M * M⁻¹)
    (hmod :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ M * M⁻¹) :
    IsUnit M := by
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨a, ha⟩ := hmod
  let Q : FractionalIdeal A⁰ K := M * M⁻¹
  change algebraMap A K (f ^ n) ∈ Q at hn
  change algebraMap A K (1 - f * a) ∈ Q at ha
  let z : A := f * a
  let s : A := ∑ i ∈ Finset.range n, z ^ i
  have hzpow : algebraMap A K (z ^ n) ∈ Q := by
    have h := Q.val.smul_mem (a ^ n) hn
    simpa [z, Algebra.smul_def, mul_pow, mul_comm] using h
  have hgeom : s * (1 - z) = 1 - z ^ n := by
    dsimp [s]
    rw [mul_comm]
    simpa using (Commute.one_right z).mul_neg_geom_sum₂ n
  have htail : algebraMap A K (1 - z ^ n) ∈ Q := by
    have ha' : algebraMap A K (1 - z) ∈ Q := by
      simpa [z] using ha
    have hscaled := Q.val.smul_mem s ha'
    have hmapped :
        algebraMap A K (s * (1 - z)) ∈ Q.val := by
      simpa only [Algebra.smul_def, map_mul] using hscaled
    rw [hgeom] at hmapped
    exact FractionalIdeal.mem_coe.mp hmapped
  have hone : (1 : K) ∈ Q := by
    have h := Q.val.add_mem htail hzpow
    simpa using h
  have hQ_le_one :
      Q ≤ (1 : FractionalIdeal A⁰ K) := by
    change M * M⁻¹ ≤ (1 : FractionalIdeal A⁰ K)
    simpa only [FractionalIdeal.inv_eq] using
      (FractionalIdeal.mul_one_div_le_one (I := M))
  have hQ : Q = 1 :=
    le_antisymm hQ_le_one
      ((FractionalIdeal.one_le).mpr hone)
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
  simpa [Q] using hQ
end
end MazurProof.N13TraceGluing
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
/-- A fraction field of a localization is also a fraction field of the
original domain. -/
theorem fractionRing_of_localization_fractionRing
    [IsFractionRing B K] :
    IsFractionRing A K := by
  let N := nonZeroDivisors B
  have hloc :
      IsLocalization
          (N.comap (algebraMap A B))
          K :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N K (fun x hx => by
        change x ∈ nonZeroDivisors B
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap A B) =
        nonZeroDivisors A := by
    ext a
    change
      algebraMap A B a ∈ nonZeroDivisors B ↔
        a ∈ nonZeroDivisors A
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      ((IsLocalization.injective B
          (submonoid_le_nonZeroDivisors (A := A) (B := B) M)).ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- The induced endomorphism of the common fraction field is the identity. -/
theorem fractionFieldMap_eq_id :
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M) =
      RingHom.id K := by
  apply IsLocalization.ringHom_ext A⁰
  apply DFunLike.ext _ _
  intro a
  change
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M)
        (algebraMap A K a) =
      algebraMap A K a
  rw [IsLocalization.map_eq]
  exact (IsScalarTower.algebraMap_apply A B K a).symm
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Every section of a fractional ideal maps into its localization. -/
theorem mem_extendFractional_of_mem
    {I : FractionalIdeal A⁰ K} {x : K}
    (hx : x ∈ I) :
    x ∈ extendFractional (A := A) (B := B) (K := K) M I := by
  change
    x ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I
  rw [FractionalIdeal.mem_extended_iff]
  apply Submodule.subset_span
  refine ⟨x, hx, ?_⟩
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
  rfl
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Extension of the multiplier inverse is contained in the inverse of
the extended fractional ideal. -/
theorem extendFractional_inv_le
    {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ ≤
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  intro z hz
  change
    z ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹ at hz
  rw [FractionalIdeal.mem_extended_iff] at hz
  refine Submodule.span_induction
    (p := fun z _ =>
      z ∈
        (extendFractional (A := A) (B := B) (K := K) M I)⁻¹)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rw [FractionalIdeal.mem_inv_iff hExtended]
    intro x hx
    change
      x ∈ FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M) I at hx
    rw [FractionalIdeal.mem_extended_iff] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        y * x ∈ (1 : FractionalIdeal B⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
      obtain ⟨r, hr⟩ :=
        (FractionalIdeal.mem_one_iff A⁰).mp
          ((FractionalIdeal.mem_inv_iff hI).mp hy a ha)
      apply (FractionalIdeal.mem_one_iff B⁰).mpr
      refine ⟨algebraMap A B r, ?_⟩
      rw [← IsScalarTower.algebraMap_apply A B K]
      exact hr
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).add_mem ha hb
    · intro a b _ hb
      have hsmul :=
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).smul_mem a hb
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hsmul
  · exact FractionalIdeal.zero_mem _
  · intro a b _ _ ha hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).add_mem ha hb
  · intro a b _ hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).smul_mem a hb
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Finite generation clears one common localization denominator and gives
the reverse inclusion for multiplier inverses. -/
theorem inv_extendFractional_le
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ ≤
      extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  obtain ⟨n, g, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  intro z hz
  have hgI (i : Fin n) : g i ∈ I := by
    change g i ∈ I.coeToSubmodule
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzg (i : Fin n) :
      z * g i ∈ (1 : FractionalIdeal B⁰ K) := by
    exact
      (FractionalIdeal.mem_inv_iff hExtended).mp hz
        (g i)
        (mem_extendFractional_of_mem
          (A := A) (B := B) (K := K) M (hgI i))
  choose b hb using fun i =>
    (FractionalIdeal.mem_one_iff B⁰).mp (hzg i)
  obtain ⟨s, hs⟩ :=
    IsLocalization.exist_integer_multiples_of_finite M b
  choose a ha using fun i => hs i
  have hszInv :
      (s : A) • z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI]
    intro x hx
    change x ∈ I.coeToSubmodule at hx
    rw [← hspan] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        ((s : A) • z) * x ∈
          (1 : FractionalIdeal A⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      apply (FractionalIdeal.mem_one_iff A⁰).mpr
      refine ⟨a i, ?_⟩
      calc
        algebraMap A K (a i) =
            algebraMap B K (algebraMap A B (a i)) := by
              rw [IsScalarTower.algebraMap_apply A B K]
        _ = algebraMap B K ((s : A) • b i) := by rw [ha i]
        _ = (s : A) • algebraMap B K (b i) := by
              simp only [Algebra.smul_def]
              rw [map_mul,
                IsScalarTower.algebraMap_apply A B K]
        _ = (s : A) • (z * g i) := by rw [hb i]
        _ = ((s : A) • z) * g i := by
              simp [Algebra.smul_def, mul_assoc]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem hx hy
    · intro r x _ hx
      have hrx :=
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem r hx
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hrx
  have hszExtended :
      (s : A) • z ∈
        extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
    change
      (s : A) • z ∈
        FractionalIdeal.extended
          K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹
    rw [FractionalIdeal.mem_extended_iff]
    apply Submodule.subset_span
    refine ⟨(s : A) • z, hszInv, ?_⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rfl
  exact
    (IsLocalization.smul_mem_iff
      (R := A) (R' := B)
      (N' :=
        (extendFractional (A := A) (B := B) (K := K) M I⁻¹ :
          Submodule B K))
      (s := s)).mp hszExtended
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Extension through a localization commutes with multiplier inverse for
every nonzero finitely generated fractional ideal. -/
theorem extendFractional_inv
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ =
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :=
  le_antisymm
    (extendFractional_inv_le (A := A) (B := B) (K := K) M hI)
    (inv_extendFractional_le
      (A := A) (B := B) (K := K) M hI hfg)
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- If a finitely generated fractional ideal becomes invertible after
localization, one element of the localization submonoid lies in `I I⁻¹`. -/
theorem exists_submonoid_mem_mul_inv
    (I : FractionalIdeal A⁰ K)
    (hfg : I.coeToSubmodule.FG)
    (hlocal :
      IsUnit
        (extendFractional (A := A) (B := B) (K := K) M I)) :
    ∃ s : M, algebraMap A K (s : A) ∈ I * I⁻¹ := by
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    hlocal.ne_zero
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hI : I ≠ 0 := by
    intro hzero
    apply hExtended
    rw [hzero]
    exact map_zero
      (extendFractional (A := A) (B := B) (K := K) M)
  have hExtMul :
      extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) =
        1 := by
    rw [map_mul,
      extendFractional_inv
        (A := A) (B := B) (K := K) M hI hfg]
    exact
      (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hlocal
  have hone :
      (1 : K) ∈
        extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) := by
    rw [hExtMul]
    simp
  change
    (1 : K) ∈
      FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M)
          (I * I⁻¹) at hone
  rw [FractionalIdeal.mem_extended_iff] at hone
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M] at hone
  have hone' :
      (1 : K) ∈
        Submodule.span B (I * I⁻¹ : Set K) := by
    simpa using hone
  obtain ⟨s, hs⟩ :=
    multiple_mem_span_of_mem_localization_span
      M B (I * I⁻¹ : Set K) (1 : K) hone'
  refine ⟨s, ?_⟩
  change
    s • (1 : K) ∈
      Submodule.span A
        ((((I * I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K)) : Set K) at hs
  rw [Submodule.span_eq] at hs
  change
    algebraMap A K (s : A) ∈
      ((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K)
  simpa only [Submonoid.smul_def, Algebra.smul_def, mul_one] using hs
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
omit M in
/-- An ideal that is invertible after localizing at powers of `f` is
already invertible when `f` is a unit modulo that ideal. -/
theorem ideal_isUnit_of_localized_isUnit
    (f : A)
    [IsLocalization (Submonoid.powers f) B]
    (I : Ideal A)
    (hfg : I.FG)
    (hmod : ∃ a : A, 1 - f * a ∈ I)
    (hlocal :
      IsUnit
        (extendFractional
          (A := A) (B := B) (K := K)
          (Submonoid.powers f)
          (I : FractionalIdeal A⁰ K))) :
    IsUnit (I : FractionalIdeal A⁰ K) := by
  let IF : FractionalIdeal A⁰ K :=
    (I : FractionalIdeal A⁰ K)
  have hfgF : IF.coeToSubmodule.FG := by
    change
      ((I : FractionalIdeal A⁰ K) :
        Submodule A K).FG
    rw [FractionalIdeal.coeIdeal_fg A⁰
      (IsFractionRing.injective A K)]
    exact hfg
  obtain ⟨s, hs⟩ :=
    exists_submonoid_mem_mul_inv
      (A := A) (B := B) (K := K)
      (Submonoid.powers f) IF hfgF hlocal
  obtain ⟨n, hn⟩ := s.2
  have hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ IF * IF⁻¹ := by
    refine ⟨n, ?_⟩
    simpa only [hn] using hs
  obtain ⟨a, ha⟩ := hmod
  have hmod' :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ IF * IF⁻¹ := by
    refine ⟨a, ?_⟩
    exact
      FractionalIdeal.coe_ideal_le_self_mul_inv K I
        (FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha)
  exact
    N13TraceGluing.isUnit_of_genericPower_and_modUniformizerTrace
      IF hpow hmod'
end
end MazurProof.N13LocalizationIdealPatch
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
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restricting the contracted infinity closure back to `D(t)` recovers the
localized affine ideal exactly. -/
theorem map_infinityClosure
    (I : Ideal AffineCurve) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (infinityClosure I) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
  simpa [infinityClosure] using
    (IsLocalization.map_under
      (R := InfinityCurve)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
      InfinityOverlap
      (Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap I))
end
end MazurProof.N13FiniteAffineTwoChart
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
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Weighted reflection in the infinity variable converts a monic affine
equation into the same equation on the overlap, up to the invertible power
of `x = t⁻¹`. -/
theorem infinityReflect_mul_xPow_on_overlap
    (p : R₂[X]) :
    (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass
            (p.reflect p.natDegree)) *
        N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom p) := by
  letI : Invertible N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.invertible
  have hinv :
      ⅟N13OrdinaryCurveOverlap.xOverlap =
        N13OrdinaryCurveOverlap.tOverlap := by
    exact
      invOf_eq_right_inv
        (by simp [mul_comm])
  have hreflect :=
    Polynomial.eval₂_reflect_mul_pow
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
      N13OrdinaryCurveOverlap.xOverlap
      p.natDegree p le_rfl
  rw [hinv] at hreflect
  rw [show
      N13IntegralInfinityReduction.integralBaseClass
          (p.reflect p.natDegree) =
        N13IntegralInfinityGraphJacobian.xClassHom
          (p.reflect p.natDegree) by rfl,
    N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom]
  simpa [N13OrdinaryCurveOverlap.affineCoeffMap] using hreflect
end
end MazurProof.N13FiniteAffineTwoChart
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
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A monic polynomial reflects at its degree to a polynomial with constant
coefficient one.  Separating that constant term exposes the infinity
uniformizer needed by the patching argument. -/
theorem reflect_natDegree_eq_one_add_X_mul
    (p : R₂[X]) (hp : p.Monic) :
    p.reflect p.natDegree =
      1 + X * (p.reflect p.natDegree).divX := by
  have hcoeff :
      (p.reflect p.natDegree).coeff 0 = 1 := by
    rw [Polynomial.coeff_reflect]
    simpa using hp.coeff_natDegree
  calc
    p.reflect p.natDegree =
        X * (p.reflect p.natDegree).divX +
          C ((p.reflect p.natDegree).coeff 0) :=
      (Polynomial.X_mul_divX_add _).symm
    _ = 1 + X * (p.reflect p.natDegree).divX := by
      rw [hcoeff, C_1]
      ring
end
end MazurProof.N13FiniteAffineTwoChart
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
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Finite affine support forces the infinity coordinate `t` to be a unit
modulo the contracted infinity closure.  A monic equation for `x` reflects
to a relation with constant coefficient one in `t`. -/
theorem infinityClosure_tUnitMod_of_finite
    (I : Ideal AffineCurve)
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    ∃ a : InfinityCurve,
      1 - N13IntegralInfinityChart.tClass * a ∈
        infinityClosure I := by
  letI : Module.Finite R₂ (AffineCurve ⧸ I) :=
    hfinite
  let xbar : AffineCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  obtain ⟨p, hpMonic, hpEval⟩ :=
    IsIntegral.of_finite R₂ xbar
  have hpMem :
      N13GeneralizedMumfordIntegral.xClassHom p ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass p) = 0
    rw [← N13ConcreteGraphRecovery.quotient_aeval_integralX]
    exact hpEval
  let r : R₂[X] :=
    p.reflect p.natDegree
  have hrMem :
      N13IntegralInfinityReduction.integralBaseClass r ∈
        infinityClosure I := by
    change
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass r) ∈
        Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I
    have hpMap :
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
            (N13GeneralizedMumfordIntegral.xClassHom p) ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I :=
      Ideal.mem_map_of_mem
        N13OrdinaryCurveOverlap.affineToInfinityOverlap hpMem
    have hprod :
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass r) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I := by
      change
        (algebraMap InfinityCurve InfinityOverlap)
              (N13IntegralInfinityReduction.integralBaseClass
                (p.reflect p.natDegree)) *
            N13OrdinaryCurveOverlap.xOverlap ^ p.natDegree ∈
          Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I
      rw [infinityReflect_mul_xPow_on_overlap p]
      exact hpMap
    exact
      (Ideal.unit_mul_mem_iff_mem
        (Ideal.map
          N13OrdinaryCurveOverlap.affineToInfinityOverlap I)
        (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow
          p.natDegree)).mp
        (by simpa [mul_comm] using hprod)
  let q : InfinityCurve :=
    -N13IntegralInfinityReduction.integralBaseClass r.divX
  refine ⟨q, ?_⟩
  change
    N13IntegralInfinityReduction.integralBaseClass
        (p.reflect p.natDegree) ∈
      infinityClosure I at hrMem
  rw [reflect_natDegree_eq_one_add_X_mul p hpMonic] at hrMem
  convert hrMem using 1
  simp only [q, N13IntegralInfinityReduction.integralBaseClass,
    map_add, map_mul, map_one]
  rw [show
    (algebraMap
        N13IntegralInfinityReduction.IntegralBase
        N13IntegralInfinityReduction.IntegralRing) X =
      N13IntegralInfinityChart.tClass by rfl]
  rw [mul_neg, sub_neg_eq_add]
end
end MazurProof.N13FiniteAffineTwoChart
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
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- An invertible affine divisor with finite support has an invertible
closure on the ordinary infinity chart.

The finite quotient supplies a monic equation for the affine coordinate.
After reflection, that equation makes `t` a unit modulo the infinity
closure; invertibility on `D(t)` then patches across `t = 0`. -/
theorem infinityClosure_isUnit_of_finite
    (I : Ideal AffineCurve)
    (hI : IsUnit (I : AffineFractionalIdeal))
    (hfinite :
      Module.Finite R₂ (AffineCurve ⧸ I)) :
    IsUnit
      (infinityClosure I : InfinityFractionalIdeal) := by
  letI : Algebra
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
    N13IntegralFractionalHull.integralToRational.toAlgebra
  letI : IsFractionRing
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
    N13IntegralFractionalHull.functionField_isFractionRing
  let K := FractionRing InfinityOverlap
  letI : Algebra AffineCurve InfinityOverlap :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap.toAlgebra
  letI : IsLocalization
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
      InfinityOverlap := by
    let e :
        N13OrdinaryCurveOverlap.AffineOverlap ≃ₐ[AffineCurve]
          InfinityOverlap :=
      { N13OrdinaryCurveOverlap.overlapEquiv with
        commutes' := fun z =>
          N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap z }
    exact
      IsLocalization.isLocalization_of_algEquiv
        (Submonoid.powers N13OrdinaryCurveOverlap.xClass) e
  letI : IsFractionRing AffineCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := AffineCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
  letI : IsFractionRing InfinityCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := InfinityCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
  have hAffineK :
      IsUnit (I : FractionalIdeal AffineCurve⁰ K) := by
    let e :=
      FractionalIdeal.canonicalEquiv
        AffineCurve⁰ AffineFunctionField K
    have hmap := hI.map e.toRingHom
    change
      IsUnit
        (e (I : FractionalIdeal AffineCurve⁰ AffineFunctionField)) at hmap
    rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
    exact hmap
  have hAffineOverlap :
      IsUnit
        (Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap I :
          FractionalIdeal InfinityOverlap⁰ K) := by
    have hmap :=
      hAffineK.map
        (N13LocalizationIdealPatch.extendFractional
          (A := AffineCurve) (B := InfinityOverlap) (K := K)
          (Submonoid.powers N13OrdinaryCurveOverlap.xClass))
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map] at hmap
    exact hmap
  have hmod :=
    infinityClosure_tUnitMod_of_finite I hfinite
  have hInfinityK :
      IsUnit
        (infinityClosure I :
          FractionalIdeal InfinityCurve⁰ K) := by
    apply
      N13LocalizationIdealPatch.ideal_isUnit_of_localized_isUnit
        (A := InfinityCurve) (B := InfinityOverlap) (K := K)
        N13IntegralInfinityChart.tClass
        (infinityClosure I)
        (infinityClosure I).fg_of_isNoetherianRing
        hmod
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map,
      map_infinityClosure]
    exact hAffineOverlap
  let e :=
    FractionalIdeal.canonicalEquiv
      InfinityCurve⁰ K N13IntegralInfinityPointSpread.FunctionField
  have hmap := hInfinityK.map e.toRingHom
  change
    IsUnit
      (e (infinityClosure I :
        FractionalIdeal InfinityCurve⁰ K)) at hmap
  rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
  exact hmap
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (I : Ideal MazurProof.N13FiniteAffineTwoChart.AffineCurve)
    (hI : IsUnit (I : MazurProof.N13FiniteAffineTwoChart.AffineFractionalIdeal))
    (hfinite :
      Module.Finite MazurProof.N13FiniteAffineTwoChart.R₂ (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸ I)) :
    IsUnit
      (MazurProof.N13FiniteAffineTwoChart.infinityClosure I : MazurProof.N13FiniteAffineTwoChart.InfinityFractionalIdeal) := by
  exact MazurProof.N13FiniteAffineTwoChart.infinityClosure_isUnit_of_finite I hI hfinite
