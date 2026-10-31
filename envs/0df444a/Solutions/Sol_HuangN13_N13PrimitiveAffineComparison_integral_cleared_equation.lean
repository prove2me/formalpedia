-- Prove2me | solution 1 for HuangN13.N13PrimitiveAffineComparison.integral_cleared_equation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:11:45.446207+00:00
-- url     : https://prove2.me/submissions/d40398aa-0e69-49a4-b051-c8330bf93858

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13QuadraticTwoChartSpreadSaturation_mul_scalar_saturated_of_left_isUnit

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
namespace MazurProof.N13PrimitiveAffineComparison
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InvertibleReductionSaturation
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR MazurProof.N13PrimitiveAffineComparison.instIsFractionRingAF
private theorem coe_principal_isUnit (a : A) (ha : a ≠ 0) :
    IsUnit ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F) := by
  refine ⟨Units.mkOfMulEqOne
    ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F)
    (((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F)⁻¹) ?_, rfl⟩
  exact FractionalIdeal.coe_ideal_span_singleton_mul_inv F ha
end
end MazurProof.N13PrimitiveAffineComparison
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
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem scalar_span_eq_one (n : ℕ) :
    FractionalIdeal.spanSingleton R⁰ ((2 : F) ^ n) = (1 : Frac) := by
  have hu : IsUnit ((2 : R) ^ n) := by
    have hq : IsUnit ((2 : Q₂) ^ n) :=
      isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
    simpa only [map_pow, map_ofNat] using hq.map (algebraMap Q₂ R)
  calc
    FractionalIdeal.spanSingleton R⁰ ((2 : F) ^ n) =
        ((Ideal.span ({(2 : R) ^ n} : Set R) : Ideal R) : Frac) := by
          rw [FractionalIdeal.coeIdeal_span_singleton]
          simp only [map_pow, map_ofNat]
    _ = 1 := by rw [Ideal.span_singleton_eq_top.mpr hu]; exact FractionalIdeal.coeIdeal_top R⁰
end
end MazurProof.N13PrimitiveAffineComparison
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR
theorem generic_cleared_equation
    (L M : Line) (f : Fˣ) (n m : ℕ) (a b : A)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hprincipal : genericIdealUnit L * toPrincipalIdeal R F f = genericIdealUnit M) :
    Ideal.map N13IntegralFractionalHull.integralToRational
        (Ideal.span ({a} : Set A) * L.affineIdeal) =
      Ideal.map N13IntegralFractionalHull.integralToRational
        (Ideal.span ({b} : Set A) * M.affineIdeal) := by
  have hfrac := congrArg (fun U : Fracˣ => (U : Frac)) hprincipal
  simp only [Units.val_mul, coe_genericIdealUnit, coe_toPrincipalIdeal] at hfrac
  have hsp := congrArg (FractionalIdeal.spanSingleton R⁰) hf
  simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton] at hsp
  rw [scalar_span_eq_one, scalar_span_eq_one, one_mul, one_mul] at hsp
  apply FractionalIdeal.coeIdeal_injective (K := F)
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap A F a) *
      ((Ideal.map N13IntegralFractionalHull.integralToRational L.affineIdeal : Ideal R) : Frac) =
    FractionalIdeal.spanSingleton R⁰ (algebraMap A F b) *
      ((Ideal.map N13IntegralFractionalHull.integralToRational M.affineIdeal : Ideal R) : Frac)
  rw [← hsp, ← hfrac]
  ac_rfl
end
end MazurProof.N13PrimitiveAffineComparison
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem affine_two_ne_zero : algebraMap R₂ A (2 : R₂) ≠ 0 := by
  change (2 : A) ≠ 0
  have h2 : (2 : R) ≠ 0 := by
    have hq : (2 : Q₂) ≠ 0 := by norm_num
    simpa only [map_ofNat, map_zero] using (algebraMap Q₂ R).injective.ne hq
  intro h
  apply h2
  simpa only [map_ofNat, map_zero] using congrArg N13IntegralFractionalHull.integralToRational h
end
end MazurProof.N13PrimitiveAffineComparison
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR MazurProof.N13PrimitiveAffineComparison.instIsFractionRingAF
theorem primitive_principal_saturated (a : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0) :
    ∀ r : R₂, r ≠ 0 → ∀ x : A,
      algebraMap R₂ A r * x ∈ Ideal.span ({a} : Set A) → x ∈ Ideal.span ({a} : Set A) := by
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have har : Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
      (Ideal.span ({a} : Set A)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton]
    intro h
    apply ha
    have hm : N13GeneralizedMumfordReduction.reduceCoordinate a ∈
        Ideal.span ({N13GeneralizedMumfordReduction.reduceCoordinate a} :
          Set N13GeneralizedMumfordReduction.SpecialRing) :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [h, Ideal.mem_bot] at hm
    exact hm
  exact twoAdic_scalar_saturated_of_reduction_ne_bot (K := F)
    N13GeneralizedMumfordReduction.reduceCoordinate affine_two_ne_zero
    N13GeneralizedMumfordReduction.ker_reduceCoordinate _
    (coe_principal_isUnit a ha0) har
end
end MazurProof.N13PrimitiveAffineComparison
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
  have hg := generic_cleared_equation L M f n m a b hf hprincipal
  have hs (c : A) (hc : N13GeneralizedMumfordReduction.reduceCoordinate c ≠ 0)
      (N : Line) (hN : AffineVerticallySaturated N) :=
    N13QuadraticTwoChartSpreadSaturation.mul_scalar_saturated_of_left_isUnit
      (Ideal.span ({c} : Set A)) N.affineIdeal
      (coe_principal_isUnit c (fun h => hc (by simp [h])))
      (primitive_principal_saturated c hc) hN
  have descend (I J : Ideal A)
      (hJ : ∀ r : R₂, r ≠ 0 → ∀ x : A, algebraMap R₂ A r * x ∈ J → x ∈ J)
      (heq : Ideal.map N13IntegralFractionalHull.integralToRational I =
        Ideal.map N13IntegralFractionalHull.integralToRational J) : I ≤ J := by
    intro x hx
    have hm := Ideal.mem_map_of_mem N13IntegralFractionalHull.integralToRational hx
    rw [heq] at hm
    change algebraMap A R x ∈ Ideal.map (algebraMap A R) J at hm
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      N13IntegralModelContraction.verticalScalars] at hm
    obtain ⟨s, hs, hsx⟩ := hm
    obtain ⟨r, hr, hrs⟩ := hs
    rw [← hrs] at hsx
    exact hJ r (mem_nonZeroDivisors_iff_ne_zero.mp hr) x hsx
  exact le_antisymm (descend _ _ (hs b hb M hM) hg)
    (descend _ _ (hs a ha L hL) hg.symm)
end
end MazurProof.N13PrimitiveAffineComparison
end
end

open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (L M : MazurProof.N13TwoChartPicardRealization.Line)
    (hL : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated L) (hM : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated M)
    (f : MazurProof.N13PrincipalBranchIdeals.Fˣ) (n m : ℕ) (a b : MazurProof.N13OverlapBranchCompatibility.A)
    (ha : MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0)
    (hf : (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ m * (f : MazurProof.N13PrincipalBranchIdeals.F) * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F b =
      (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ n * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F a)
    (hprincipal : MazurProof.N13TwoChartPicardRealization.genericIdealUnit L * toPrincipalIdeal MazurProof.N13PrincipalBranchIdeals.R MazurProof.N13PrincipalBranchIdeals.F f = MazurProof.N13TwoChartPicardRealization.genericIdealUnit M) :
    Ideal.span ({a} : Set MazurProof.N13OverlapBranchCompatibility.A) * L.affineIdeal =
      Ideal.span ({b} : Set MazurProof.N13OverlapBranchCompatibility.A) * M.affineIdeal := by
  exact MazurProof.N13PrimitiveAffineComparison.integral_cleared_equation L M hL hM f n m a b ha hb hf hprincipal
