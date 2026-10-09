-- Prove2me | solution 1 for MazurProof.N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:15:21.926172+00:00
-- url     : https://prove2.me/submissions/f0240344-21e7-4129-a4b7-9397a1633148

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)
@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num
@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp
@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction =====
section
/-!
# Reduction of integral N13 Mumford graphs at two

The good integral equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

has the same coefficients after reduction from `ℤ₂` to `𝔽₂`.  Hence
coefficientwise reduction induces a canonical ring homomorphism between
the two affine coordinate rings.  This file proves that the homomorphism
preserves both coordinates and carries every generalized Mumford graph
ideal exactly to the corresponding special-fibre graph ideal.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)
/-- Coefficientwise reduction of polynomials is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)
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
theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
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

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toSextic_algebraMap (z : K) :
    toSextic (K := K)
        (algebraMap K (GoodRing (K := K)) z) =
      algebraMap K (SexticRing (K := K)) z := by
  change
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass (C z)) =
      SexticMumford.xClass (M (K := K)) (C z)
  exact toSextic_xClass (K := K) (C z)
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralModelContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]
attribute [local instance] MazurProof.N13IntegralModelContraction.goodRingLocalization
attribute [local instance] MazurProof.N13IntegralModelContraction.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.rationalRingLocalization
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

-- ===== FLT.Assumptions.MazurProof.N13QuotientReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientReduction =====
section
/-!
# Reduction of N13 affine quotients

A surjective ambient reduction map descends along a literal mapped-ideal
equality.  The kernel of the descended map is exactly the image of the
ambient kernel.  For the N13 integral model this is the principal ideal
generated by the quotient class of `2`.

No flatness, saturation, or chosen Mumford presentation is used here.
-/
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
attribute [local instance] MazurProof.N13QuotientReduction.instFactPrimeOfNatNat_fLT
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

-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/
open Polynomial
namespace MazurProof.N13CanonicalContractionQuotient
noncomputable section
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.integralRationalAlgebra
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

-- ===== FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness =====
section
/-!
# Vertical saturation gives flat N13 quotients

The canonical contraction of a generic ideal is saturated with respect to
every nonzero two-adic scalar.  Consequently its affine quotient has no
two-adic torsion.  Since the two-adic integers form a Dedekind domain, the
quotient is flat even before finiteness has been established.

This separates the easy vertical part of the two-fibre argument from the
genuine no-escape/finiteness step.
-/
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
attribute [local instance] MazurProof.N13QuotientVerticalFlatness.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13QuotientVerticalFlatness.integralRationalAlgebra
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

-- ===== FLT.Assumptions.MazurProof.N13TensorSpecialFiber =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TensorSpecialFiber =====
section
/-!
# Identifying a tensor special fibre from its quotient map

Suppose a surjective quotient-reduction map has kernel generated by the
image of a uniformizer.  Tensoring with the residue field then gives the
target quotient exactly.  The proof uses pure tensors and moves the
uniformizer to the residue-field factor; it does not identify a separate
quotient of the source ideal.
-/
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
section ResidueField
variable [IsLocalRing R]
variable [Algebra (IsLocalRing.ResidueField R) C]
variable [IsScalarTower R (IsLocalRing.ResidueField R) C]
@[simp] theorem residueLinearEquiv_tmul
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap (IsLocalRing.ResidueField R) C).comp (IsLocalRing.residue R))
    (π : R)
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hg : Function.Surjective g)
    (hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R B π} : Set B))
    (a : (IsLocalRing.ResidueField R)) (b : B) :
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
section BasisTransport
variable {ι : Type uι}
theorem mk_eq_pullbackBasis
    (e : k ⊗[R] B ≃ₗ[k] C)
    (v : ι → B)
    (bC : Basis ι k C)
    (heval :
      ∀ i : ι,
        e (TensorProduct.mk R k B 1 (v i)) = bC i) :
    ∀ i : ι,
      TensorProduct.mk R k B 1 (v i) =
        pullbackBasis e bC i := by
  intro i
  apply e.injective
  simpa [pullbackBasis] using heval i
end BasisTransport
end
end MazurProof.N13TensorSpecialFiber
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis =====
section
-- ===== FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis =====
section
/-!
# The concrete two-fibre basis for an N13 contraction

Assume only the remaining representative-level statement that the canonical
contraction reduces to the fixed special graph ideal.  The generic and special
quotient frames are then both literally `{1,x}`.  The two-fibre no-escape
theorem therefore makes the same pair an integral basis, without any prior
finiteness assumption.
-/
open Polynomial
open Module
open scoped TensorProduct
namespace MazurProof.N13TwoFiberConcreteBasis
noncomputable section
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.integralRationalAlgebra
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.baseSpecialAlgebra
attribute [local instance] MazurProof.N13TwoFiberConcreteBasis.baseSpecialQuotientTower
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
        (N13GeneralizedMumfordIntegral.xClass (C r)) =
      N13GoodCoordinateRingTwo.xClass
        (C (N13GeneralizedMumfordReduction.reduceBase r))
  rw [N13GeneralizedMumfordReduction.reduce_xClass]
  simp [N13GeneralizedMumfordReduction.reducePoly]
universe uR uK uB uG uι
end
end MazurProof.N13TwoFiberConcreteBasis
end

end

-- ===== FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift =====
section
/-!
# Lifting the literal special-fibre basis `{1,x}`

For a finite flat algebra over a local ring, a family whose residue-field
base change is a basis is already a basis over the local ring.  This file
specializes the structural local lifting theorem to the literal family
`{1,x}` needed by the N13 quotient.
-/
open scoped TensorProduct
open Module
namespace MazurProof.N13FiniteFlatBasisLift
noncomputable section
universe uR uB
variable {R : Type uR} {B : Type uB}
variable [CommRing R] [IsLocalRing R]
variable [CommRing B] [Algebra R B]
variable [Module.Finite R B] [Module.Flat R B]
/--
If `{1,x}` becomes a supplied basis after residue-field base change, then
the same literal family is a basis over the local ring.
-/
theorem exists_basis_oneX
    (x : B)
    (b₀ : Basis (Fin 2) (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 (oneX x i) = b₀ i) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = oneX x := by
  have hfamily :
      (TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 ∘ oneX x) =
        (b₀ : Fin 2 → (IsLocalRing.ResidueField R) ⊗[R] B) := by
    funext i
    exact hb₀ i
  have hk :
      Function.Bijective
        (Finsupp.linearCombination (IsLocalRing.ResidueField R)
          (TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 ∘ oneX x)) := by
    rw [hfamily]
    exact
      ⟨b₀.linearIndependent,
        fun y => ⟨b₀.repr y, b₀.linearCombination_repr y⟩⟩
  have hR :
      Function.Bijective
        (Finsupp.linearCombination R (oneX x)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat
      (R := R) (M := B) (oneX x) hk
  have hspan :
      ⊤ ≤ Submodule.span R (Set.range (oneX x)) := by
    rw [← Finsupp.range_linearCombination]
    exact (LinearMap.range_eq_top.mpr hR.2).ge
  refine ⟨Basis.mk hR.1 hspan, ?_⟩
  exact Basis.coe_mk hR.1 hspan
end
end MazurProof.N13FiniteFlatBasisLift
end

end

-- ===== FLT.Assumptions.MazurProof.N13GenericQuotientLocalization =====
section
-- ===== FLT.Assumptions.MazurProof.N13GenericQuotientLocalization =====
section
/-!
# The generic fibre of a canonical N13 contraction

The quotient by a canonical vertical contraction becomes the original
Mumford quotient after inverting the nonzero two-adic scalars.  Consequently,
a contracted quadratic Mumford quotient has rank two over the two-adic
integers.  No preferred integral basis is used.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13GenericQuotientLocalization
noncomputable section
attribute [local instance] MazurProof.N13GenericQuotientLocalization.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13GenericQuotientLocalization.integralRationalAlgebra
attribute [local instance] MazurProof.N13GenericQuotientLocalization.rationalRingLocalization
/-- The generic quotient map is localization at the nonzero two-adic
scalars. -/
theorem genericQuotient_isLocalized
    (J : Ideal RationalRing) :
    IsLocalizedModule (nonZeroDivisors R₂)
      (genericQuotientAlgHom J).toLinearMap := by
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hs :
          algebraMap R₂ Q₂ (s : R₂) ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      apply_fun
        (fun z : G ↦
          (algebraMap R₂ Q₂ (s : R₂))⁻¹ • z) at hxy
      simpa [Module.algebraMap_end_apply,
        ← IsScalarTower.algebraMap_smul Q₂, hs] using hxy
    · intro y
      let c : Q₂ := algebraMap R₂ Q₂ (s : R₂)
      have hc : c ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      refine ⟨c⁻¹ • y, ?_⟩
      change c • (c⁻¹ • y) = y
      exact smul_inv_smul₀ hc y
  · intro y
    obtain ⟨z, rfl⟩ :=
      Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, hz⟩ :=
      IsLocalization.surj
        N13IntegralModelContraction.verticalScalars z
    obtain ⟨r, hr, hs⟩ := s.property
    refine
      ⟨⟨Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a,
          ⟨r, hr⟩⟩,
        ?_⟩
    change
      r • Ideal.Quotient.mk J z =
        N13CanonicalContractionQuotient.genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a)
    rw [N13CanonicalContractionQuotient.genericQuotientMap_mk,
      Algebra.smul_def]
    change
      Ideal.Quotient.mk J
          (algebraMap R₂ RationalRing r * z) =
        Ideal.Quotient.mk J
          (N13TwoAdicCoordinateBaseChange.integralToSextic a)
    apply congrArg (Ideal.Quotient.mk J)
    rw [mul_comm]
    calc
      z * algebraMap R₂ RationalRing r =
          z *
            N13TwoAdicCoordinateBaseChange.integralToSextic
              (s : IntegralRing) := by
        rw [← hs]
        congr 1
        symm
        change
          N13GoodSexticCoordinateEquiv.toSextic
              (N13IntegralModelContraction.integralToGood
                (algebraMap R₂ IntegralRing r)) =
            algebraMap R₂ RationalRing r
        rw [N13IntegralModelContraction.integralToGood_algebraMap,
          N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
        exact
          (IsScalarTower.algebraMap_apply
            R₂ Q₂ RationalRing r).symm
      _ = N13TwoAdicCoordinateBaseChange.integralToSextic a := hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact
      N13CanonicalContractionQuotient.genericQuotientMap_injective J hxy
/-- A quadratic generic Mumford quotient forces its canonical contracted
quotient to have rank two over the two-adic integers. -/
theorem contractQuotient_finrank_eq_two
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    Module.finrank R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (SexticMumford.mumfordIdeal Model D.u D.v)) =
      2 := by
  let J : Ideal RationalRing :=
    SexticMumford.mumfordIdeal Model D.u D.v
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  let q : B →ₗ[R₂] G :=
    (genericQuotientAlgHom J).toLinearMap
  letI : IsLocalizedModule (nonZeroDivisors R₂) q :=
    genericQuotient_isLocalized J
  have hloc :
      Module.finrank R₂ G =
        Module.finrank R₂ B :=
    IsLocalizedModule.finrank_eq
      (nonZeroDivisors R₂) q le_rfl
  have hrank :
      Module.rank Q₂ G =
        Module.rank R₂ G :=
    IsLocalization.rank_eq
      Q₂ (nonZeroDivisors R₂) le_rfl
  have hfield :
      Module.finrank Q₂ G =
        Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hgeneric :
      Module.finrank Q₂ G = 2 := by
    rw [Module.finrank_eq_card_basis
      (SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)]
    rfl
  change Module.finrank R₂ B = 2
  calc
    Module.finrank R₂ B =
        Module.finrank R₂ G := hloc.symm
    _ = Module.finrank Q₂ G := hfield.symm
    _ = 2 := hgeneric
end
end MazurProof.N13GenericQuotientLocalization
end

end

-- ===== FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis =====
section
/-!
# A two-generator basis dichotomy in dimension two

The special N13 affine coordinate ring, and every one of its quotients, is
generated by the literal coordinates `x` and `y`.  In a two-dimensional
quotient over a field, this implies structurally that either `{1,x}` or
`{1,y}` is a basis.
-/
open Module
open Polynomial
namespace MazurProof.N13TwoGeneratorFiberBasis
noncomputable section
universe uK uB
variable {K : Type uK} {B : Type uB}
variable [Field K] [CommRing B] [Algebra K B] [Nontrivial B]
/-- If a two-dimensional algebra is generated by `x` and `y`, then one of
`{1,x}` and `{1,y}` is linearly independent. -/
theorem oneX_or_oneY_linearIndependent
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    LinearIndependent K ![1, x] ∨
      LinearIndependent K ![1, y] := by
  by_contra h
  have hxNot : ¬ LinearIndependent K ![1, x] :=
    fun hx ↦ h (Or.inl hx)
  have hyNot : ¬ LinearIndependent K ![1, y] :=
    fun hy ↦ h (Or.inr hy)
  have hx :
      ∃ a : K, algebraMap K B a = x := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hxNot
    push Not at hxNot
    obtain ⟨a, ha⟩ := hxNot
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
  have hy :
      ∃ b : K, algebraMap K B b = y := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hyNot
    push Not at hyNot
    obtain ⟨b, hb⟩ := hyNot
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hbot : (⊥ : Subalgebra K B) = ⊤ := by
    apply top_unique
    rw [← hgen, Algebra.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro z
    have hz : z ∈ (⊥ : Subalgebra K B) := by
      rw [hbot]
      trivial
    simpa only [Algebra.mem_bot, Set.mem_range] using hz
  have hbij :
      Function.Bijective (algebraMap K B) :=
    ⟨FaithfulSMul.algebraMap_injective K B, hsurj⟩
  have hrank :
      Module.finrank K B = 1 :=
    Module.finrank_of_bijective_algebraMap hbij
  omega
/-- Basis-valued form of `oneX_or_oneY_linearIndependent`. -/
theorem exists_basis_oneX_or_oneY
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, x]) ∨
      (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, y]) := by
  rcases oneX_or_oneY_linearIndependent x y hfinrank hgen with hx | hy
  · left
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hx (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
  · right
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hy (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
/-- Every polynomial in the special `x` coordinate lies in the subalgebra
generated by the literal `x` and `y` coordinates. -/
theorem xClass_mem_coordinateAdjoin
    (p : SpecialField[X]) :
    N13GoodCoordinateRingTwo.xClass p ∈
      Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) := by
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.xClass p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [N13GoodCoordinateRingTwo.xClass_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,
        N13GoodCoordinateRingTwo.xClass_mul,
        N13GoodCoordinateRingTwo.xClass_pow]
      apply S.mul_mem
      · change algebraMap SpecialField SpecialRing a ∈ S
        exact S.algebraMap_mem a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert
              (N13GoodCoordinateRingTwo.xClass X)
              {N13GoodCoordinateRingTwo.yClass}))
          n
/-- The special affine coordinate ring is generated by its literal
coordinates. -/
theorem coordinate_adjoin_eq_top :
    Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) =
      ⊤ := by
  apply Algebra.eq_top_iff.2
  intro z
  obtain ⟨p, rfl⟩ :=
    AdjoinRoot.mk_surjective z
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.mk p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change
        N13GoodCoordinateRingTwo.xClass a *
            N13GoodCoordinateRingTwo.yClass ^ n ∈ S
      apply S.mul_mem
      · exact xClass_mem_coordinateAdjoin a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert_iff.mpr
              (Or.inr
                (Set.mem_singleton
                  N13GoodCoordinateRingTwo.yClass))))
          n
/-- Every quotient of the special affine coordinate ring is still generated
by the images of its literal coordinates. -/
theorem quotient_coordinate_adjoin_eq_top
    (I : Ideal SpecialRing) :
    Algebra.adjoin SpecialField
        ({Ideal.Quotient.mk I
            (N13GoodCoordinateRingTwo.xClass X),
          Ideal.Quotient.mk I
            N13GoodCoordinateRingTwo.yClass} :
          Set (SpecialRing ⧸ I)) =
      ⊤ := by
  let π : SpecialRing →ₐ[SpecialField] SpecialRing ⧸ I :=
    Ideal.Quotient.mkₐ SpecialField I
  rw [show
    ({Ideal.Quotient.mk I
        (N13GoodCoordinateRingTwo.xClass X),
      Ideal.Quotient.mk I
        N13GoodCoordinateRingTwo.yClass} :
      Set (SpecialRing ⧸ I)) =
      π ''
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) by
    exact
      (Set.image_pair π
        (N13GoodCoordinateRingTwo.xClass X)
        N13GoodCoordinateRingTwo.yClass).symm]
  rw [← AlgHom.map_adjoin, coordinate_adjoin_eq_top,
    Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective
end
end MazurProof.N13TwoGeneratorFiberBasis
end

end

-- ===== FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis =====
section
-- ===== FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis =====
section
open Module
open Polynomial
open scoped TensorProduct
/-!
# Coordinate bases for finite quadratic contractions

For a finite canonical contraction of a quadratic N13 Mumford quotient,
the special fibre is a two-dimensional algebra generated by the literal
coordinates `x` and `y`.  Thus either `{1,x}` or `{1,y}` is a basis on the
special fibre.  Finite flat lifting gives the same literal alternative
over the two-adic integers.
-/
namespace MazurProof.N13ContractQuotientXYBasis
noncomputable section
universe uF uK uA uι
theorem exists_basis_restrictScalars_of_surjective
    {F : Type uF} {K : Type uK} {A : Type uA} {ι : Type uι}
    [Field F] [Field K] [CommRing A]
    [Algebra F K] [Algebra F A] [Algebra K A]
    [IsScalarTower F K A] [Fintype ι]
    (hFK : Function.Surjective (algebraMap F K))
    (b : Basis ι K A) :
    ∃ bF : Basis ι F A, (bF : ι → A) = b := by
  have hli :
      LinearIndependent F (b : ι → A) :=
    b.linearIndependent.restrict_scalars' F
  have hspan :
      ⊤ ≤ Submodule.span F (Set.range (b : ι → A)) := by
    intro z _
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨a, ha⟩ := hFK (b.repr z i)
    rw [← ha, IsScalarTower.algebraMap_smul K]
    exact
      Submodule.smul_mem _ a
        (Submodule.subset_span (Set.mem_range_self i))
  let bF : Basis ι F A :=
    Basis.mk hli hspan
  exact ⟨bF, Basis.coe_mk hli hspan⟩
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.baseSpecialAlgebra
theorem specialQuotientMap_comp_algebraMap
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I J hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k (SpecialRing ⧸ J)).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J
        (algebraMap k SpecialRing
          (N13GeneralizedMumfordReduction.reduceBase r))
  congr 1
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C r)) =
      N13GoodCoordinateRingTwo.xClass
        (C (N13GeneralizedMumfordReduction.reduceBase r))
  rw [N13GeneralizedMumfordReduction.reduce_xClass]
  simp [N13GeneralizedMumfordReduction.reducePoly]
theorem exists_contractQuotient_basis_oneX_or_oneY
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    (∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13CanonicalContractionQuotient.integralX)) ∨
      (∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            integralY)) := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let J : Ideal SpecialRing :=
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate I
  let B := IntegralRing ⧸ I
  let C := SpecialRing ⧸ J
  let g : B →+* C :=
    N13QuotientReduction.reduceCoordinateQuotient I J rfl
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_flat
      (N13CanonicalContractionQuotient.graphIdeal D)
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  letI : IsScalarTower R₂ k C :=
    IsScalarTower.of_algebraMap_eq
      (R := R₂) (S := k) (A := C) fun _ => rfl
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap k C).comp (algebraMap R₂ k) := by
    exact specialQuotientMap_comp_algebraMap I J rfl
  have hg : Function.Surjective g :=
    N13QuotientReduction.reduceCoordinateQuotient_surjective
      I J rfl
  have hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    N13QuotientReduction.ker_reduceCoordinateQuotient_eq_span_two
      I J rfl
  let eK : k ⊗[R₂] B ≃ₗ[k] C :=
    N13TensorSpecialFiber.tensorLinearEquiv
      (g := g)
      (hfactor := hfactor)
      (hq := ZMod.ringHom_surjective PadicInt.toZMod)
      (π := (2 : R₂))
      (hπ := N13GeneralizedMumfordReduction.reduceBase_two)
      (hg := hg)
      (hker := hker)
  have hfinB : Module.finrank R₂ B = 2 := by
    exact
      N13GenericQuotientLocalization.contractQuotient_finrank_eq_two
        D hdeg
  have hfinC : Module.finrank k C = 2 := by
    rw [← eK.finrank_eq, Module.finrank_baseChange, hfinB]
  letI : Nontrivial C :=
    Module.nontrivial_of_finrank_pos
      (R := k) (M := C) (by rw [hfinC]; decide)
  let xB : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let yB : B :=
    Ideal.Quotient.mk I integralY
  let xC : C :=
    Ideal.Quotient.mk J
      (N13GoodCoordinateRingTwo.xClass X)
  let yC : C :=
    Ideal.Quotient.mk J
      N13GoodCoordinateRingTwo.yClass
  have hgen :
      Algebra.adjoin k ({xC, yC} : Set C) = ⊤ := by
    exact
      N13TwoGeneratorFiberBasis.quotient_coordinate_adjoin_eq_top J
  have hexC :=
    N13TwoGeneratorFiberBasis.exists_basis_oneX_or_oneY
      xC yC hfinC hgen
  have hfactorκ :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ C).comp (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k C (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R₂ C r :=
        (IsScalarTower.algebraMap_apply R₂ k C r).symm
      _ = algebraMap κ C (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply R₂ κ C r
      _ = algebraMap κ C
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let eκ : κ ⊗[R₂] B ≃ₗ[κ] C :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactorκ (2 : R₂) htwo hg hker
  have eκ_tmul_one (b : B) :
      eκ (TensorProduct.mk R₂ κ B 1 b) = g b := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactorκ (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] b) = g b
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactorκ)
        (π := (2 : R₂))
        (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) b)
  have hκk :
      Function.Surjective (algebraMap κ k) := by
    intro a
    obtain ⟨r, hr⟩ :=
      ZMod.ringHom_surjective PadicInt.toZMod a
    refine ⟨IsLocalRing.residue R₂ r, ?_⟩
    calc
      algebraMap κ k (IsLocalRing.residue R₂ r) =
          algebraMap R₂ k r := by
        exact
          (IsScalarTower.algebraMap_apply R₂ κ k r).symm
      _ = a := hr
  have ex_map :
      g xB = xC := by
    change
      N13QuotientReduction.reduceCoordinateQuotient I J rfl
          (Ideal.Quotient.mk I
            N13CanonicalContractionQuotient.integralX) =
        xC
    rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
      N13CanonicalContractionQuotient.integralX,
      N13GeneralizedMumfordReduction.reduce_xClass]
    simp [xC, N13GeneralizedMumfordReduction.reducePoly,
      N13GeneralizedMumfordReduction.reduceBase]
  have ey_map :
      g yB = yC := by
    change
      N13QuotientReduction.reduceCoordinateQuotient I J rfl
          (Ideal.Quotient.mk I integralY) =
        yC
    rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
      integralY,
      N13GeneralizedMumfordReduction.reduce_yClass]
  rcases hexC with ⟨bC, hbC⟩ | ⟨bC, hbC⟩
  · left
    obtain ⟨bCκ, hbCκ⟩ :=
      exists_basis_restrictScalars_of_surjective hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX xB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ex_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX xB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX xB) bCκ heval i
    simpa [I, B, xB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) xB b₀ hb₀
  · right
    obtain ⟨bCκ, hbCκ⟩ :=
      exists_basis_restrictScalars_of_surjective hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX yB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ey_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX yB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX yB) bCκ heval i
    simpa [I, B, yB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) yB b₀ hb₀
end
end MazurProof.N13ContractQuotientXYBasis
end

end

theorem solution : type_of% @MazurProof.N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY := @MazurProof.N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
