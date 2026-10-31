-- Prove2me | solution 1 for HuangN13.N13ConcreteGraphRecovery.exists_diskPair_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:56:07.822973+00:00
-- url     : https://prove2.me/submissions/86491b6f-9c76-4d40-b285-07dbd923fdf5

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_HuangN13_N13ConcreteGraphRecovery_exists_integral_diskGraph
import Theorems.Thm_MazurProof_N13CanonicalContractionQuotient_genericQuotientMap_comp_algebraMap
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_N13SpecialQuotientBasis_specialData_u_natDegree

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
  change (_root_.Polynomial.C p %ₘ curvePoly).coeff 0 = p
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
/-- Coefficientwise reduction of polynomials is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)
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
/-- The integral good-model coordinate ring reduces onto its special fibre.
This follows from the common rank-two normal form, not from a presentation
calculation in the quotient. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeffY z)
  refine ⟨
    N13GeneralizedMumfordIntegral.xClass p +
      N13GeneralizedMumfordIntegral.xClass q *
        N13GeneralizedMumfordIntegral.yClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
    hp, hq]
  exact N13GoodCoordinateRingTwo.recompose z
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
    ∃ q : R₂[X], p = _root_.Polynomial.C (2 : R₂) * q := by
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
      N13GeneralizedMumfordIntegral.xClass (_root_.Polynomial.C 2 * p) +
          N13GeneralizedMumfordIntegral.xClass (_root_.Polynomial.C 2 * q) *
            N13GeneralizedMumfordIntegral.yClass =
        N13GeneralizedMumfordIntegral.xClass (_root_.Polynomial.C 2) *
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
      (N13GeneralizedMumfordIntegral.xClass (_root_.Polynomial.C (2 : R₂))) = 0
    rw [reduce_xClass]
    simp [reducePoly]
end
end MazurProof.N13GeneralizedMumfordReduction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralModelContraction.integralRationalAlgebra MazurProof.N13IntegralModelContraction.rationalRingLocalization
/-- The contracted ideal is saturated with respect to every nonzero
vertical scalar. -/
theorem contractIdeal_vertical_saturated
    (J : Ideal RationalRing)
    {a : IntegralRing}
    (r : R₂) (hr : r ≠ 0)
    (ha :
      algebraMap R₂ IntegralRing r * a ∈
        contractIdeal J) :
    a ∈ contractIdeal J := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (algebraMap R₂ IntegralRing r * a) ∈ J at ha
  rw [map_mul] at ha
  let s : verticalScalars :=
    ⟨algebraMap R₂ IntegralRing r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩
  have hs :
      IsUnit
        (algebraMap IntegralRing RationalRing s) :=
    IsLocalization.map_units RationalRing s
  exact (Ideal.unit_mul_mem_iff_mem J hs).mp ha
end
end MazurProof.N13IntegralModelContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- Surjectivity descends to the quotient rings. -/
theorem inducedQuotientMap_surjective
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    Function.Surjective
      (inducedQuotientMap f I J hmap) := by
  unfold inducedQuotientMap
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective.comp hf
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- For a surjective ambient map, the quotient kernel is the image of the
ambient kernel. -/
theorem ker_inducedQuotientMap_eq_map_ker
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.map (Ideal.Quotient.mk I) (RingHom.ker f) := by
  have hkerComp :
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
        I ⊔ RingHom.ker f := by
    calc
      RingHom.ker ((Ideal.Quotient.mk J).comp f) =
          Ideal.comap f
            (RingHom.ker (Ideal.Quotient.mk J)) :=
        (RingHom.comap_ker (Ideal.Quotient.mk J) f).symm
      _ = Ideal.comap f J := by
        rw [Ideal.mk_ker]
      _ = Ideal.comap f (Ideal.map f I) :=
        congrArg (Ideal.comap f) hmap.symm
      _ = I ⊔ Ideal.comap f (⊥ : Ideal S) :=
        Ideal.comap_map_of_surjective f hf I
      _ = I ⊔ RingHom.ker f := by
        rfl
  unfold inducedQuotientMap
  rw [Ideal.ker_quotient_lift, hkerComp,
    Ideal.map_sup, Ideal.map_quotient_self]
  simp
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- A principal ambient kernel remains principal after quotienting. -/
theorem ker_inducedQuotientMap_eq_span
    (f : A →+* S)
    (hf : Function.Surjective f)
    (I : Ideal A)
    (J : Ideal S)
    (hmap : Ideal.map f I = J)
    (r : A)
    (hker :
      RingHom.ker f = Ideal.span ({r} : Set A)) :
    RingHom.ker (inducedQuotientMap f I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I r} : Set (A ⧸ I)) := by
  rw [ker_inducedQuotientMap_eq_map_ker
      f hf I J hmap,
    hker, Ideal.map_span]
  simp
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
theorem reduceCoordinateQuotient_surjective
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    Function.Surjective
      (reduceCoordinateQuotient I J hmap) := by
  exact
    inducedQuotientMap_surjective
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- The descended N13 reduction kernel is generated by the quotient class
of the vertical parameter `2`. -/
theorem ker_reduceCoordinateQuotient
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({Ideal.Quotient.mk I
            (algebraMap R₂ IntegralRing (2 : R₂))} :
          Set (IntegralRing ⧸ I)) := by
  exact
    ker_inducedQuotientMap_eq_span
      N13GeneralizedMumfordReduction.reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective
      I J hmap
      (algebraMap R₂ IntegralRing (2 : R₂))
      N13GeneralizedMumfordReduction.ker_reduceCoordinate
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientReduction
noncomputable section
universe uA uS
variable {A : Type uA} {S : Type uS}
variable [CommRing A] [CommRing S]
/-- Equivalent scalar-algebra-map spelling of the same kernel. -/
theorem ker_reduceCoordinateQuotient_eq_span_two
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    RingHom.ker (reduceCoordinateQuotient I J hmap) =
      Ideal.span
        ({algebraMap R₂ (IntegralRing ⧸ I) (2 : R₂)} :
          Set (IntegralRing ⧸ I)) := by
  simpa only [Ideal.Quotient.mk_algebraMap] using
    ker_reduceCoordinateQuotient I J hmap
end
end MazurProof.N13QuotientReduction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13CanonicalContractionQuotient
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- No element is lost when passing from the contracted quotient to the
generic quotient. -/
theorem genericQuotientMap_injective
    (J : Ideal RationalRing) :
    Function.Injective (genericQuotientMap J) := by
  intro z w hzw
  apply sub_eq_zero.mp
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective (z - w)
  rw [← ha]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  calc
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic a) =
        genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a) := rfl
    _ = genericQuotientMap J (z - w) :=
      congrArg (genericQuotientMap J) ha
    _ = genericQuotientMap J z -
        genericQuotientMap J w := map_sub _ z w
    _ = 0 := by rw [hzw, sub_self]
end
end MazurProof.N13CanonicalContractionQuotient
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientVerticalFlatness
noncomputable section
universe uR uA
variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]
/--
An ideal saturated with respect to every nonzero base scalar has a
torsion-free quotient over the base.
-/
theorem quotient_isTorsionFree_of_scalar_saturated
    (I : Ideal A)
    (hsaturated :
      ∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) :
    Module.IsTorsionFree R (A ⧸ I) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturated r hr a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    change
      algebraMap R (A ⧸ I) r *
          Ideal.Quotient.mk I a = 0
    simpa only [Algebra.smul_def] using hrz
end
end MazurProof.N13QuotientVerticalFlatness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientVerticalFlatness
noncomputable section
universe uR uA
variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The quotient by a canonical vertical contraction is two-adically
torsion-free. -/
theorem contractQuotient_isTorsionFree
    (J : Ideal RationalRing) :
    Module.IsTorsionFree R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  apply quotient_isTorsionFree_of_scalar_saturated
  intro r hr a ha
  exact
    N13IntegralModelContraction.contractIdeal_vertical_saturated
      J r hr ha
end
end MazurProof.N13QuotientVerticalFlatness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13QuotientVerticalFlatness
noncomputable section
universe uR uA
variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Over the two-adic DVR the same quotient is flat, with no finiteness
assumption. -/
theorem contractQuotient_flat
    (J : Ideal RationalRing) :
    Module.Flat R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  letI :
      Module.IsTorsionFree R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal J) :=
    contractQuotient_isTorsionFree J
  infer_instance
end
end MazurProof.N13QuotientVerticalFlatness
end
end

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13TensorSpecialFiber
noncomputable section
universe uR uk uB uC uι
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
@[simp] theorem tensorLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hq : Function.Surjective (algebraMap R k))
    (π : R)
    (hπ : algebraMap R k π = 0)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : k) (b : B) :
    tensorLinearEquiv g hfactor hq π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact tensorLinearMap_tmul g hfactor a b
end
end MazurProof.N13TensorSpecialFiber
end
end

section
section
set_option autoImplicit false
open scoped TensorProduct
open Module
namespace MazurProof.N13TensorSpecialFiber
noncomputable section
universe uR uk uB uC uι
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [CommRing k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
section ResidueField
variable [IsLocalRing R]
local notation "κ" => IsLocalRing.ResidueField R
variable [Algebra (IsLocalRing.ResidueField R) C]
variable [IsScalarTower R (IsLocalRing.ResidueField R) C]
@[simp] theorem residueLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap κ C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : κ) (b : B) :
    residueLinearEquiv g hfactor π hπ hg hker
        (a ⊗ₜ[R] b) =
      a • g b := by
  exact
    tensorLinearEquiv_tmul
      (g := g)
      (hfactor := residueFactor g hfactor)
      (hq := residueAlgebraMap_surjective (R := R))
      (π := π)
      (hπ := residueElement_eq_zero π hπ)
      (hg := hg)
      (hker := hker)
      a b
end ResidueField
end
end MazurProof.N13TensorSpecialFiber
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
theorem residueBasis_apply (i : Fin 2) :
    residueBasis i =
      AdjoinRoot.root specialData.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
        (finCongr specialData_u_natDegree)) i =
      AdjoinRoot.root specialData.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl
end
end MazurProof.N13SpecialQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
@[simp] theorem residueBasis_zero :
    residueBasis (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]
end
end MazurProof.N13SpecialQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
@[simp] theorem residueBasis_one :
    residueBasis (1 : Fin 2) =
      AdjoinRoot.root specialData.u := by
  simp [residueBasis_apply]
end
end MazurProof.N13SpecialQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
@[simp] theorem quotientBasis_zero :
    quotientBasis (0 : Fin 2) = 1 := by
  change quotientAlgEquiv.symm (residueBasis 0) = 1
  rw [residueBasis_zero]
  exact map_one quotientAlgEquiv.symm
end
end MazurProof.N13SpecialQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem quotientBasis_one :
    quotientBasis (1 : Fin 2) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X) := by
  change
    quotientAlgEquiv.symm (residueBasis 1) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X)
  rw [residueBasis_one]
  apply quotientAlgEquiv.injective
  rw [quotientAlgEquiv.apply_symm_apply]
  simp only [quotientAlgEquiv]
  change
    AdjoinRoot.root specialData.u =
      N13GoodCoordinateRingTwo.mumfordEval specialData
        (N13GoodCoordinateRingTwo.xClass X)
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass]
  rfl
end
end MazurProof.N13SpecialQuotientBasis
end
end

section
section
set_option autoImplicit false
open Module
namespace MazurProof.N13TwoFiberNoEscape
noncomputable section
universe uR uk uB uC
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]
@[simp] theorem pairFamily_zero (e₀ e₁ : B) :
    pairFamily e₀ e₁ (0 : Fin 2) = e₀ := by
  simp [pairFamily]
end
end MazurProof.N13TwoFiberNoEscape
end
end

section
section
set_option autoImplicit false
open Module
namespace MazurProof.N13TwoFiberNoEscape
noncomputable section
universe uR uk uB uC
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]
@[simp] theorem pairFamily_one (e₀ e₁ : B) :
    pairFamily e₀ e₁ (1 : Fin 2) = e₁ := by
  simp [pairFamily]
end
end MazurProof.N13TwoFiberNoEscape
end
end

section
section
set_option autoImplicit false
open Module
namespace MazurProof.N13TwoFiberNoEscape
noncomputable section
universe uR uk uB uC
variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]
section FractionFieldClearing
universe uK uG
variable {K : Type uK} {G : Type uG}
variable [Field K] [CommRing G]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra R G] [Algebra K G]
variable [IsScalarTower R K G]
/--
Two coefficients in the fraction field admit one common nonzero
denominator.
-/
theorem exists_common_denominator
    (α₀ α₁ : K) :
    ∃ r : R, r ≠ 0 ∧
      ∃ a₀ a₁ : R,
        algebraMap R K r * α₀ = algebraMap R K a₀ ∧
        algebraMap R K r * α₁ = algebraMap R K a₁ := by
  obtain ⟨b₀, d₀, hd₀, hα₀⟩ :=
    IsFractionRing.div_surjective R α₀
  obtain ⟨b₁, d₁, hd₁, hα₁⟩ :=
    IsFractionRing.div_surjective R α₁
  have hd₀_ne : d₀ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₀
  have hd₁_ne : d₁ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₁
  have hmapd₀ : algebraMap R K d₀ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₀_ne
  have hmapd₁ : algebraMap R K d₁ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₁_ne
  refine ⟨d₀ * d₁, mul_ne_zero hd₀_ne hd₁_ne,
    b₀ * d₁, b₁ * d₀, ?_, ?_⟩
  · rw [← hα₀]
    push_cast
    field_simp
  · rw [← hα₁]
    push_cast
    field_simp
end FractionFieldClearing
end
end MazurProof.N13TwoFiberNoEscape
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13TwoFiberConcreteBasis.baseSpecialAlgebra MazurProof.N13TwoFiberConcreteBasis.instFactPrimeOfNatNat_fLT
/-- The descended reduction map respects the chosen composite
`R₂ → k → SpecialQuotient` scalar structure. -/
theorem specialQuotientMap_comp_algebraMap
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k SpecialQuotient).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (algebraMap k SpecialRing
          (N13GeneralizedMumfordReduction.reduceBase r))
  congr 1
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (_root_.Polynomial.C r)) =
      N13GoodCoordinateRingTwo.xClass
        (_root_.Polynomial.C (N13GeneralizedMumfordReduction.reduceBase r))
  rw [N13GeneralizedMumfordReduction.reduce_xClass]
  simp [N13GeneralizedMumfordReduction.reducePoly]
end
end MazurProof.N13TwoFiberConcreteBasis
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Reduction sends the integral class of `x` to the first fixed special
basis vector. -/
theorem specialQuotientMap_x_eq_basis_one
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) =
      N13SpecialQuotientBasis.quotientBasis 1 := by
  rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
    N13CanonicalContractionQuotient.integralX,
    N13GeneralizedMumfordReduction.reduce_xClass,
    N13SpecialQuotientBasis.quotientBasis_one]
  simp [N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]
end
end MazurProof.N13TwoFiberConcreteBasis
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13TwoFiberConcreteBasis.baseSpecialAlgebra MazurProof.N13TwoFiberConcreteBasis.baseSpecialQuotientTower MazurProof.N13TwoFiberConcreteBasis.instFactPrimeOfNatNat_fLT
/-- A literal fixed special fibre forces the integral classes `{1,x}` in
the contracted quotient to be linearly independent.  Flatness lifts the
independence from the residue-field tensor product; no generic degree
hypothesis is used. -/
theorem integralPair_linearIndependent
    (D : SexticMumford.SemiMumford Model)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    LinearIndependent R₂
      (N13TwoFiberNoEscape.pairFamily
        (1 :
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))
          N13CanonicalContractionQuotient.integralX)) := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let g :=
    N13QuotientReduction.reduceCoordinateQuotient
      I N13SpecialQuotientBasis.specialIdeal hmap
  let e₀ : B := 1
  let e₁ : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ SpecialQuotient).comp
          (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k SpecialQuotient
            (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply, g, B] using
          DFunLike.congr_fun
            (specialQuotientMap_comp_algebraMap I hmap) r
      _ = algebraMap R₂ SpecialQuotient r :=
        (IsScalarTower.algebraMap_apply
          R₂ k SpecialQuotient r).symm
      _ = algebraMap κ SpecialQuotient
          (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply
          R₂ κ SpecialQuotient r
      _ = algebraMap κ SpecialQuotient
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let hg :
      Function.Surjective g :=
    N13QuotientReduction.reduceCoordinateQuotient_surjective
      I N13SpecialQuotientBasis.specialIdeal hmap
  let hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    N13QuotientReduction.ker_reduceCoordinateQuotient_eq_span_two
      I N13SpecialQuotientBasis.specialIdeal hmap
  let e :
      κ ⊗[R₂] B ≃ₗ[κ] SpecialQuotient :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactor (2 : R₂) htwo hg hker
  have hliSpecial :
      LinearIndependent κ
        (N13SpecialQuotientBasis.quotientBasis :
          Fin 2 → SpecialQuotient) :=
    N13SpecialQuotientBasis.quotientBasis.linearIndependent
      |>.restrict_scalars' κ
  have e_tmul_one (b : B) :
      e (TensorProduct.mk R₂ κ B 1 b) = g b := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactor (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] b) = g b
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactor)
        (π := (2 : R₂)) (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) b)
  have heval (i : Fin 2) :
      e
          (TensorProduct.mk R₂ κ B 1
            (N13TwoFiberNoEscape.pairFamily e₀ e₁ i)) =
        N13SpecialQuotientBasis.quotientBasis i := by
    rw [e_tmul_one]
    fin_cases i
    · simp [e₀, g]
    · simpa [e₁, g] using
        specialQuotientMap_x_eq_basis_one I hmap
  have hliTensor :
      LinearIndependent κ
        (TensorProduct.mk R₂ κ B 1 ∘
          N13TwoFiberNoEscape.pairFamily e₀ e₁) := by
    apply LinearIndependent.of_comp e.toLinearMap
    convert hliSpecial using 1
    funext i
    exact heval i
  letI : Module.Flat R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_flat
      (N13CanonicalContractionQuotient.graphIdeal D)
  exact
    IsLocalRing.linearIndependent_of_flat
      (N13TwoFiberNoEscape.pairFamily e₀ e₁) hliTensor
end
end MazurProof.N13TwoFiberConcreteBasis
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
universe uR uK uB uG uι
/-- Clear one common denominator in a finite generic relation and descend
it through an injective integral algebra map. -/
theorem linearIndependent_map_to_fractionField
    {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] [Algebra R K]
    {B : Type uB} [CommRing B] [Algebra R B]
    {G : Type uG} [CommRing G]
    [Algebra R G] [Algebra K G] [IsScalarTower R K G]
    {ι : Type uι} [Fintype ι]
    (hRK : Function.Injective (algebraMap R K))
    (q : B →ₐ[R] G) (hq : Function.Injective q)
    (v : ι → B)
    (hden :
      ∀ c : ι → K,
        ∃ d : R, d ≠ 0 ∧ ∃ a : ι → R,
          ∀ i,
            algebraMap R K (a i) =
              algebraMap R K d * c i)
    (hv : LinearIndependent R v) :
    LinearIndependent K (fun i => q (v i)) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  obtain ⟨d, hd, a, ha⟩ := hden c
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using hRK.ne hd
  have hscaled :
      ∑ j, algebraMap R K (a j) • q (v j) = 0 := by
    calc
      ∑ j, algebraMap R K (a j) • q (v j) =
          ∑ j, (algebraMap R K d * c j) • q (v j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ha j]
      _ = ∑ j, algebraMap R K d •
          (c j • q (v j)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [smul_smul]
      _ = algebraMap R K d •
          ∑ j, c j • q (v j) := by
            rw [Finset.smul_sum]
      _ = 0 := by rw [hc, smul_zero]
  have hqsum :
      q (∑ j, a j • v j) = 0 := by
    calc
      q (∑ j, a j • v j) =
          ∑ j, q (a j • v j) := by simp
      _ = ∑ j, a j • q (v j) := by simp
      _ = ∑ j, algebraMap R K (a j) •
          q (v j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Algebra.smul_def, Algebra.smul_def,
              IsScalarTower.algebraMap_apply R K G]
      _ = 0 := hscaled
  have hint : ∑ j, a j • v j = 0 := by
    apply hq
    simpa only [map_zero] using hqsum
  have hai : a i = 0 := hv a hint i
  have hprod : algebraMap R K d * c i = 0 := by
    rw [← ha i, hai, map_zero]
  exact (mul_eq_zero.mp hprod).resolve_left hdK
end
end MazurProof.N13TwoFiberConcreteBasis
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
universe uR uK uB uG uι
/-- A linearly independent pair in an algebra linearly equivalent to a
monic polynomial quotient forces polynomial degree at least two. -/
theorem natDegree_ge_two_of_linearIndependent_fin_two
    {K : Type uK} [Field K]
    (u : K[X]) (hu : u.Monic)
    {B : Type uB} [AddCommGroup B] [Module K B]
    (e : B ≃ₗ[K] AdjoinRoot u)
    {v : Fin 2 → B}
    (hv : LinearIndependent K v) :
    2 ≤ u.natDegree := by
  letI : Module.Finite K (AdjoinRoot u) :=
    hu.finite_adjoinRoot
  have hv' :
      LinearIndependent K (fun i => e (v i)) := by
    change LinearIndependent K (e ∘ v)
    exact
      hv.map' e.toLinearMap
        (LinearMap.ker_eq_bot_of_injective e.injective)
  calc
    2 = Fintype.card (Fin 2) := by simp
    _ ≤ Module.finrank K (AdjoinRoot u) :=
      hv'.fintype_card_le_finrank
    _ = u.natDegree :=
      (AdjoinRoot.powerBasis' hu).finrank
end
end MazurProof.N13TwoFiberConcreteBasis
end
end

section
section
set_option autoImplicit false
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
universe uR uK uB uG uι
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The literal two-dimensional special fibre itself forces the generic
Mumford polynomial to have degree two, provided only the balanced upper
bound. -/
theorem degree_eq_two_of_map_contractIdeal_eq_special
    (D : SexticMumford.SemiMumford Model)
    (hdeg_le : D.u.natDegree ≤ 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    D.u.natDegree = 2 := by
  let J :=
    N13CanonicalContractionQuotient.graphIdeal D
  let I :=
    N13IntegralModelContraction.contractIdeal J
  let B := IntegralRing ⧸ I
  let G := RationalRing ⧸ J
  let v : Fin 2 → B :=
    N13TwoFiberNoEscape.pairFamily
      1
      (Ideal.Quotient.mk I
        N13CanonicalContractionQuotient.integralX)
  let q : B →ₐ[R₂] G :=
    { toRingHom :=
        N13CanonicalContractionQuotient.genericQuotientMap J
      commutes' := fun r => by
        change
          N13CanonicalContractionQuotient.genericQuotientMap J
              (algebraMap R₂
                (IntegralRing ⧸
                  N13IntegralModelContraction.contractIdeal J) r) =
            algebraMap R₂ (RationalRing ⧸ J) r
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun
            (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
              J) r }
  have hvR : LinearIndependent R₂ v := by
    simpa only [J, I, B, v] using
      integralPair_linearIndependent D hmap
  have hden :
      ∀ c : Fin 2 → Q₂,
        ∃ d : R₂, d ≠ 0 ∧ ∃ a : Fin 2 → R₂,
          ∀ i,
            algebraMap R₂ Q₂ (a i) =
              algebraMap R₂ Q₂ d * c i := by
    intro c
    obtain ⟨d, hd, a₀, a₁, ha₀, ha₁⟩ :=
      N13TwoFiberNoEscape.exists_common_denominator
        (R := R₂) (K := Q₂) (c 0) (c 1)
    refine ⟨d, hd,
      N13TwoFiberNoEscape.pairFamily a₀ a₁, ?_⟩
    intro i
    fin_cases i
    · simpa using ha₀.symm
    · simpa using ha₁.symm
  have hvQ :
      LinearIndependent Q₂ (fun i => q (v i)) := by
    exact
      linearIndependent_map_to_fractionField
        (hRK := IsFractionRing.injective R₂ Q₂)
        q
        (N13CanonicalContractionQuotient.genericQuotientMap_injective J)
        v hden hvR
  have hge : 2 ≤ D.u.natDegree :=
    natDegree_ge_two_of_linearIndependent_fin_two
      D.u D.u_monic
      (SexticMumford.mumfordQuotientAlgEquiv
        Model D).toLinearEquiv
      hvQ
  exact le_antisymm hdeg_le hge
end
end MazurProof.N13TwoFiberConcreteBasis
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
/-- Equal graph ideals with equal infinity multiplicity define the same
oriented Picard class.  This is the literal representative-level form of
the separatedness used below. -/
theorem semiMumfordClass_eq_of_graphIdeal_eq
    (D₁ D₂ : SexticMumford.SemiMumford Model)
    (hideal :
      N13CanonicalContractionQuotient.graphIdeal D₁ =
        N13CanonicalContractionQuotient.graphIdeal D₂)
    (hnInf : D₁.nInf = D₂.nInf) :
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₁ =
      SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₂ := by
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · apply Units.ext
    change
      (N13CanonicalContractionQuotient.graphIdeal D₁ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)) =
        (N13CanonicalContractionQuotient.graphIdeal D₂ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model))
    exact congrArg
      (fun I : Ideal
          (SexticMumford.CoordinateRing Model) ↦
        (I :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)))
      hideal
  · unfold SexticMumford.semiMumfordRaw
    rw [hnInf]
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
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A balanced quadratic representative whose canonical contraction has the
selected special graph is represented by an actual pair in the two
distinguished residue disks. -/
theorem exists_diskPair_class_eq
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ P : N13TwoAdicAbelChartData.DiskPair,
      SexticMumford.classOf
          Model (N13Infinity.positiveInfinityOrder Q₂) D =
        N13TwoAdicAbelChartPic.DiskPair.pic P := by
  have hdeg : D.u.natDegree = 2 :=
    N13TwoFiberConcreteBasis.degree_eq_two_of_map_contractIdeal_eq_special
      D.toSemi (by simpa using D.deg_u) hmap
  have hnInfNat : D.nInf = 0 := by
    have hbound := D.infinity_bound
    omega
  have hnInf : D.toSemi.nInf = 0 := by
    simp [hnInfNat]
  obtain ⟨E, P, _hEdeg, hgraph, hEP⟩ :=
    HuangN13.N13ConcreteGraphRecovery.exists_integral_diskGraph D.toSemi (by simpa using hdeg) hmap
  have hEPsextic :
      N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := by
    change
      SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi E 0).u
          (N13TwoAdicMumfordTransport.sexticSemi E 0).v =
        SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).u
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).v
    rw [
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        E 0,
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        P.smoothMumford 0]
    exact congrArg
      (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
      hEP
  have hgraphDP :
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := by
    calc
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
          N13IntegralGraphContraction.sexticIdeal
            E D.toSemi.nInf := hgraph
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) := by
        rw [hnInf]
        rfl
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := hEPsextic
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := rfl
  refine ⟨P, ?_⟩
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D.toSemi =
      SexticMumford.classOf
        Model (N13Infinity.positiveInfinityOrder Q₂)
          (N13TwoAdicAbelChartPic.DiskPair.mumford P)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  apply semiMumfordClass_eq_of_graphIdeal_eq
    D.toSemi
      (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi
      hgraphDP
  simp [hnInfNat]
end
end MazurProof.N13ConcreteGraphRecovery
end
end


set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13ConcreteGraphRecovery.Model)
    (hmap :
      Ideal.map
          MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate
          (MazurProof.N13IntegralModelContraction.contractIdeal
            (MazurProof.N13CanonicalContractionQuotient.graphIdeal D.toSemi)) =
        MazurProof.N13SpecialQuotientBasis.specialIdeal) :
    ∃ P : MazurProof.N13TwoAdicAbelChartData.DiskPair,
      MazurProof.SexticMumford.classOf
          MazurProof.N13ConcreteGraphRecovery.Model (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13ConcreteGraphRecovery.Q₂) D =
        MazurProof.N13TwoAdicAbelChartPic.DiskPair.pic P := by
  exact MazurProof.N13ConcreteGraphRecovery.exists_diskPair_class_eq D hmap
