-- Prove2me | solution 1 for MazurTransfer.order13_actual_function_field_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T22:09:15.736933+00:00
-- url     : https://prove2.me/submissions/dbc16d90-c318-45f4-a118-ddc1e11b3ed6

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Design boundary: invariants of the literal curve function field and an actual
two-affine-open cover. Named downstream consumer: the unchanged arithmetic
Picard group correspondence for the order-13 campaign branch.
Full original Picard dependencies: official Anthropic FLT, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2. Actual curve: MazurTheorem,
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. No Picard, group-law, finite-map,
or geometric-integrality assumption is added to the target.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Free
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace Order13FunctionFieldPublicProof


section
noncomputable section
open AlgebraicGeometry CategoryTheory
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicGeometry
universe u
variable (K : Type u) [Field K] (h104 : (104 : K) ≠ 0)
include h104
theorem actual_good_characteristic_geometry :
    IsIntegral (curveScheme K) ∧ SmoothOfRelativeDimension 1 (curveToBase K) ∧
      IsProper (curveToBase K) ∧ IsNoetherian (curveScheme K) :=
  _root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104
theorem curveScheme_isIntegral : IsIntegral (curveScheme K) :=
  (actual_good_characteristic_geometry K h104).1
theorem curveToBase_smooth_relativeDimension_one : SmoothOfRelativeDimension 1 (curveToBase K) :=
  (actual_good_characteristic_geometry K h104).2.1
end MazurTransfer.Order13GoodCharacteristicGeometry
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
instance actualCurve_publicSmooth : Smooth (curveToBase K) := by
  letI : SmoothOfRelativeDimension 1 (curveToBase K) :=
    Order13GoodCharacteristicGeometry.curveToBase_smooth_relativeDimension_one K Fact.out
  exact SmoothOfRelativeDimension.smooth 1 _
instance actualCurve_publicNoetherian : IsNoetherian (curveScheme K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.2
end MazurTransfer.Order13GoodCharacteristicCurveModel
end
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)

abbrev equation : Polynomial R := X ^ 2 - C f

def powerBasis : PowerBasis R (AdjoinRoot (equation R f)) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f (by decide))

theorem powerBasis_dim : (powerBasis R f).dim = 2 := by
  change (X ^ 2 - C f).natDegree = 2
  exact Polynomial.natDegree_X_pow_sub_C

def basis : Basis (Fin 2) R (AdjoinRoot (equation R f)) :=
  (powerBasis R f).basis.reindex (finCongr (powerBasis_dim R f))

theorem basis_zero : basis R f 0 = 1 := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 0).val :=
      (powerBasis R f).basis_eq_pow _
    _ = 1 := by simp

theorem basis_one : basis R f 1 = AdjoinRoot.root (equation R f) := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 1).val :=
      (powerBasis R f).basis_eq_pow _
    _ = (powerBasis R f).gen := by simp
    _ = AdjoinRoot.root (equation R f) := rfl

def coordinates : AdjoinRoot (equation R f) ≃ₗ[R] R × R :=
  (basis R f).equivFun.trans (LinearEquiv.finTwoArrow R R)

theorem coordinates_symm (v : R × R) :
    (coordinates R f).symm v = AdjoinRoot.of (equation R f) v.1 +
      AdjoinRoot.of (equation R f) v.2 * AdjoinRoot.root (equation R f) := by
  rw [coordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem coordinates_of_add_of_mul_root (a b : R) :
    coordinates R f (AdjoinRoot.of (equation R f) a +
      AdjoinRoot.of (equation R f) b * AdjoinRoot.root (equation R f)) = (a, b) := by
  rw [← coordinates_symm R f (a, b), LinearEquiv.apply_symm_apply]

end MazurTransfer.QuadraticCoordinates


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual function-field places and closed points from the
literal good-characteristic curve's checked geometry, with every geometry
instance explicit. Named downstream consumer: public effective degree-two
divisor counts. No supplied model or finite-set affine-open hypothesis is
used by this smaller place foundation.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) := Order13GoodCharacteristicGeometry.curveScheme_isIntegral K Fact.out

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) :=
  Order13GoodCharacteristicGeometry.curveToBase_smooth_relativeDimension_one K Fact.out

instance actualCurve_isProper : IsProper (curveToBase K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.1

instance actualCurve_isNoetherian : IsNoetherian (curveScheme K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.2

instance actualCurve_isSmooth : Smooth (curveToBase K) :=
  SmoothOfRelativeDimension.smooth 1 _

abbrev actualCurveFunctionField : Type u := (curveScheme K).functionField

instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

def actualPlaceOfPoint (x : closedPoints (curveScheme K)) : Place K (actualCurveFunctionField K) :=
  Classical.choose (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_stalk_range (x : closedPoints (curveScheme K)) :
    (algebraMap ((curveScheme K).presheaf.stalk x.1) (actualCurveFunctionField K)).range =
      (actualPlaceOfPoint K x).toValuationSubring.toSubring :=
  Classical.choose_spec (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_bijective : Function.Bijective (actualPlaceOfPoint K) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact _root_.AlgebraicCurve.eq_of_range_stalk_eq (curveToBase K) x.1 y.1
      (by rw [actualPlaceOfPoint_stalk_range, actualPlaceOfPoint_stalk_range, hxy])
  · intro v
    obtain ⟨x, hx, hrange⟩ :=
      _root_.AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase K) v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

instance actualFunctionFieldIsCurveOver : IsCurveOver K (actualCurveFunctionField K) :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (curveToBase K) (RingEquiv.refl _) (fun _ => rfl)

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the genuine two-affine-open cover of the unchanged glued
order-thirteen curve. Named downstream consumer: the actual structure-sheaf
section comparison with the complete official FLT Cech interface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

def ordinaryOpen : (curveScheme K).Opens := (ordinaryChartMap K).opensRange
def reciprocalOpen : (curveScheme K).Opens := (reciprocalChartMap K).opensRange

theorem chart_opens_sup_eq_top : ordinaryOpen K ⊔ reciprocalOpen K = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ Set.range (ordinaryChartMap K) ∨ x ∈ Set.range (reciprocalChartMap K)
  obtain ⟨i, y, hy⟩ := (glueData K).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem curveScheme_isSeparated : (curveScheme K).IsSeparated := by
  have h : IsSeparated (curveToBase K ≫ terminal.from (Spec (.of K))) := inferInstance
  refine ⟨?_⟩
  simpa only [terminal.comp_from] using h

def actualTwoAffineOpenCover : (curveScheme K).TwoAffineOpenCover := by
  haveI := curveScheme_isSeparated K
  exact {
    U0 := ordinaryOpen K
    U1 := reciprocalOpen K
    isAffineOpen_U0 := isAffineOpen_opensRange (ordinaryChartMap K)
    isAffineOpen_U1 := isAffineOpen_opensRange (reciprocalChartMap K)
    sup_eq_top := chart_opens_sup_eq_top K
    isAffineOpen_inf := (isAffineOpen_opensRange (ordinaryChartMap K)).inf
      (isAffineOpen_opensRange (reciprocalChartMap K)) }

end MazurTorsion.XOneThirteenProjectiveCurve

end

end


section
/- Whole official FLT proof at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Routine aliases expanded to standard opens; unused tool import and option headers omitted. Original forwarding dependencies point to the identical checked whole-source proofs. Named downstream consumer: actual order-13 scheme/place Cech comparison. -/
namespace MazurTransfer.PublicNonAffineCurveProof


open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

theorem nonAffineCurve_solution {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by
  intro hX
  haveI : IsAffineHom f := isAffineHom_of_isAffine f
  haveI hfin : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

  have hΓ : (f.appTop).hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)

  let φ : k →+* Γ(X, ⊤) := (f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφfin : φ.Finite :=
    RingHom.Finite.comp hΓ (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfield : IsField Γ(X, ⊤) := by
    letI := φ.toAlgebra
    haveI : Module.Finite k Γ(X, ⊤) := hφfin
    haveI : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
    exact (Algebra.IsIntegral.isField_iff_isField (R := k) (S := Γ(X, ⊤)) φ.injective).mp
      (Field.toIsField k)

  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    haveI := Ring.isField_iff_isSimpleOrder_ideal.mp hfield
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top p.asIdeal with hp | hp
    · rcases IsSimpleOrder.eq_bot_or_eq_top q.asIdeal with hq | hq
      · rw [hp, hq]
      · exact absurd hq q.isPrime.ne_top
    · exact absurd hp p.isPrime.ne_top
  have hsubX : Subsingleton X := by
    haveI : Subsingleton (Spec Γ(X, ⊤)) := hsub
    exact (Scheme.homeoOfIso X.isoSpec).toEquiv.subsingleton
  have hclosed : IsClosed ({genericPoint X} : Set X) := by
    have : ({genericPoint X} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [this]; exact isClosed_univ

  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk (genericPoint X)) :=
    _root_.AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
      (genericPoint X) hclosed
  exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X))
    (Field.toIsField X.functionField)

end MazurTransfer.PublicNonAffineCurveProof

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

theorem actual_curve_not_isAffine : ¬ IsAffine (curveScheme K) :=
  MazurTransfer.PublicNonAffineCurveProof.nonAffineCurve_solution
    (curveToBase K)

theorem actual_affineOpen_ne_top (U : (curveScheme K).Opens) (hU : IsAffineOpen U) :
    U ≠ ⊤ := by
  intro h
  have hT : IsAffineOpen (⊤ : (curveScheme K).Opens) := h ▸ hU
  haveI : IsAffine (⊤ : (curveScheme K).Opens) := hT
  exact actual_curve_not_isAffine K (IsAffine.of_isIso (curveScheme K).topIso.inv)

theorem actual_places_cover_nonempty_complements :
    placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0 ∪
        placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1 = Set.univ ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0) ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1) := by
  exact _root_.AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top
    (curveToBase K) (actualTwoAffineOpenCover K).U0 (actualTwoAffineOpenCover K).U1
    (actualTwoAffineOpenCover K).sup_eq_top
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U0)
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U1)

theorem actual_placesOf_inf (U V : (curveScheme K).Opens) :
    placesOf (curveToBase K) (U ⊓ V) =
      placesOf (curveToBase K) U ∩ placesOf (curveToBase K) V := by
  ext v
  constructor
  · rintro ⟨x, hx, hclosed, hrange⟩
    exact ⟨⟨x, hx.1, hclosed, hrange⟩, ⟨x, hx.2, hclosed, hrange⟩⟩
  · rintro ⟨⟨x, hxU, hxclosed, hxrange⟩, ⟨y, hyV, _, hyrange⟩⟩
    have hxy : x = y := _root_.AlgebraicCurve.eq_of_range_stalk_eq
      (curveToBase K) x y (hxrange.trans hyrange.symm)
    subst y
    exact ⟨x, ⟨hxU, hyV⟩, hxclosed, hxrange⟩

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine affine coordinate sections of an open immersion
compatible with the base-field morphism. Named downstream consumer: the actual
order-thirteen chart/overlap section comparison with the official FLT cover.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace MazurTransfer.AffineOpenCoordinateSections
universe u
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of K))
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

theorem sectionsIso_inv :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE f.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE]

def sectionsRingIso : Γ(X, f.opensRange) ≅ CommRingCat.of A :=
  (IsOpenImmersion.ΓIsoTop f).symm ≪≫ Scheme.ΓSpecIso (.of A)

theorem sectionsRingIso_hom :
    (sectionsRingIso A f).hom = f.appLE f.opensRange ⊤ (by simp) ≫
      (Scheme.ΓSpecIso (.of A)).hom := by
  simp only [sectionsRingIso, Iso.trans_hom, Iso.symm_hom, sectionsIso_inv]

theorem sectionsRingIso_commutes
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    (Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ f.opensRange (by simp) ≫
      (sectionsRingIso A f).hom = CommRingCat.ofHom (algebraMap K A) := by
  have H : c.appLE ⊤ f.opensRange (by simp) ≫ f.appLE f.opensRange ⊤ (by simp) =
      (f ≫ c).appLE ⊤ ⊤ (by simp) :=
    Scheme.Hom.appLE_comp_appLE f c ⊤ f.opensRange ⊤ (by simp) (by simp)
  have H' : (f ≫ c).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop := by
    rw [hf]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ c).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of A)).hom := by
      rw [sectionsRingIso_hom]
      simpa only [Category.assoc] using congrArg
        (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := congrArg
          (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H'
    _ = _ := by rw [Scheme.ΓSpecIso_naturality]; simp

def sectionsAlgEquiv
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
    Γ(X, f.opensRange) ≃ₐ[K] A := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
  exact AlgEquiv.ofRingEquiv
    (f := (sectionsRingIso A f).commRingCatIsoToRingEquiv) (fun k =>
      congrArg (fun t => t.hom k) (sectionsRingIso_commutes K A c f hf))

variable {B : Type u} [CommRing B]

theorem sectionsRingIso_restriction (φ : A →+* B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hg : Spec.map (CommRingCat.ofHom φ) ≫ f = g)
    (hU : g.opensRange ≤ f.opensRange) :
    X.presheaf.map (Opposite.op (homOfLE hU)) ≫ (sectionsRingIso B g).hom =
      (sectionsRingIso A f).hom ≫ CommRingCat.ofHom φ := by
  have eg : (⊤ : (Spec (.of B)).Opens) ≤ g ⁻¹ᵁ f.opensRange := by
    simpa only [Scheme.Hom.preimage_opensRange] using g.preimage_mono hU
  have Hres : X.presheaf.map (homOfLE hU).op ≫ g.appLE g.opensRange ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := Scheme.Hom.map_appLE g (by simp) (homOfLE hU).op
  have Hcomp : f.appLE f.opensRange ⊤ (by simp) ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := by
    have H := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) f
      f.opensRange ⊤ ⊤ (by simp) (by simp)
    simpa only [hg] using H
  have Htop : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom φ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = g.appLE f.opensRange ⊤ eg ≫ (Scheme.ΓSpecIso (.of B)).hom := by
      rw [sectionsRingIso_hom]
      exact congrArg (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hres
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of B)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hcomp.symm
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Scheme.ΓSpecIso (.of B)).hom := congrArg
          (fun t => f.appLE f.opensRange ⊤ (by simp) ≫ t ≫
            (Scheme.ΓSpecIso (.of B)).hom) Htop
    _ = _ := by rw [Scheme.ΓSpecIso_naturality, sectionsRingIso_hom]; simp only [Category.assoc]

def sectionsAlgEquivAt (U : X.Opens) (hU : f.opensRange = U)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X, U) ≃ₐ[K] A := by
  subst U
  exact sectionsAlgEquiv K A c f hf

theorem sectionsAlgEquivAt_restriction [Algebra K B] (φ : A →ₐ[K] B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hgf : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = g)
    (U V : X.Opens) (hU : f.opensRange = U) (hV : g.opensRange = V) (hVU : V ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    ∀ z : Γ(X, U),
      sectionsAlgEquivAt K B c g V hV hg
        (Scheme.TwoAffineOpenCover.restrictAlgHom c hVU z) =
      φ (sectionsAlgEquivAt K A c f U hU hf z) := by
  subst U
  subst V
  intro z
  exact congrArg (fun t => t.hom z) (sectionsRingIso_restriction A f φ.toRingHom g hgf hVU)

end MazurTransfer.AffineOpenCoordinateSections



end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine scheme intersection of the actual order-thirteen
charts, with the original overlap coordinate algebra and maps.
Named downstream consumer: actual structure-sheaf section comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

def ordinaryOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ _root_.MazurTorsion.XOneThirteenAffineCurve.scheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K)
    (OrdinaryOverlapRing K)))

def reciprocalOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ reciprocalScheme K :=
  Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase K).toRingHom)

def overlapToCurve : Spec (.of (OrdinaryOverlapRing K)) ⟶ curveScheme K :=
  ordinaryOverlapMap K ≫ ordinaryChartMap K

instance ordinaryOverlapMap_isOpenImmersion : IsOpenImmersion (ordinaryOverlapMap K) :=
  IsOpenImmersion.of_isLocalization (_root_.MazurTorsion.XOneThirteenAffineCurve.xCoordinate K)

instance overlapToCurve_isOpenImmersion : IsOpenImmersion (overlapToCurve K) := by
  unfold overlapToCurve
  infer_instance

theorem actual_overlap_isPullback :
    IsPullback (ordinaryOverlapMap K) (reciprocalOverlapMap K)
      (ordinaryChartMap K) (reciprocalChartMap K) := by
  classical
  have hne : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by decide
  have hnerev := Ne.symm hne
  have hv : (glueData K).V (Chart.ordinary, Chart.reciprocal) =
      Spec (.of (OrdinaryOverlapRing K)) := by
    simp only [glueData, CategoryTheory.GlueData.ofGlueData', categoricalGlueData, dif_neg hne]
  have H := IsPullback.of_isLimit
    ((glueData K).vPullbackConeIsLimit Chart.ordinary Chart.reciprocal)
  change IsPullback ((glueData K).f Chart.ordinary Chart.reciprocal)
    ((glueData K).t Chart.ordinary Chart.reciprocal ≫
      (glueData K).f Chart.reciprocal Chart.ordinary)
    (ordinaryChartMap K) (reciprocalChartMap K) at H
  have hmap : (overlapSchemeIso K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) = reciprocalOverlapMap K := by
    rw [overlapSchemeIso_hom, ← Spec.map_comp]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact reciprocalToOrdinary_algebraMap K a
  refine H.of_iso (eqToIso hv) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id,
      ordinaryOverlapMap, glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hne, overlapInclusion]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id,
      glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hne, dif_neg hnerev, overlapInclusion,
      overlapTransition, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hmap]
    rfl
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem overlapToCurve_eq_reciprocal :
    overlapToCurve K = reciprocalOverlapMap K ≫ reciprocalChartMap K :=
  (actual_overlap_isPullback K).w

theorem overlap_opensRange :
    (overlapToCurve K).opensRange = ordinaryOpen K ⊓ reciprocalOpen K := by
  have H := actual_overlap_isPullback K
  have he : H.isoPullback.hom ≫ pullback.fst (ordinaryChartMap K) (reciprocalChartMap K) ≫
      ordinaryChartMap K = overlapToCurve K := by
    rw [← Category.assoc, H.isoPullback_hom_fst]
    rfl
  apply TopologicalSpace.Opens.ext
  change Set.range (overlapToCurve K) =
    Set.range (ordinaryChartMap K) ∩ Set.range (reciprocalChartMap K)
  rw [← he]
  change Set.range ((pullback.fst (ordinaryChartMap K) (reciprocalChartMap K) ≫
    ordinaryChartMap K) ∘ H.isoPullback.hom) = _
  have hsurj : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact Scheme.Pullback.range_fst_comp _ _

end MazurTorsion.XOneThirteenProjectiveCurve

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: an actual localized quadratic coordinate algebra is
equivalent to the quadratic algebra over Laurent polynomials. Named downstream
consumer: the two-chart Cech quotient of the order-thirteen curve.
This does not assert a genus or a sheaf-cohomology comparison.
-/

noncomputable section
namespace MazurTransfer.HyperellipticLaurentOverlap
open Polynomial

variable (K : Type*) [CommRing K] (f : Polynomial K)

instance : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      Polynomial.toLaurent_C]
    exact (LaurentPolynomial.C_eq_algebraMap k).symm

def equation : Polynomial (Polynomial K) := X ^ 2 - C f
abbrev Chart := AdjoinRoot (equation K f)
def x : Chart K f := AdjoinRoot.of (equation K f) X
def y : Chart K f := AdjoinRoot.root (equation K f)
abbrev Overlap := Localization.Away (x K f)
abbrev laurentEquation : Polynomial (LaurentPolynomial K) := X ^ 2 - C f.toLaurent
abbrev LaurentChart := AdjoinRoot (laurentEquation K f)

def toLaurentBase : Chart K f →ₐ[K] LaurentChart K f :=
  AdjoinRoot.liftAlgHom (equation K f)
    ((AdjoinRoot.ofAlgHom K (laurentEquation K f)).comp Polynomial.toLaurentAlg)
    (AdjoinRoot.root (laurentEquation K f)) (by
      have h := AdjoinRoot.eval₂_root (laurentEquation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact h)

@[simp] theorem toLaurentBase_x :
    toLaurentBase K f (x K f) =
      AdjoinRoot.of (laurentEquation K f) (LaurentPolynomial.T 1) := by
  simp [toLaurentBase, x]

@[simp] theorem toLaurentBase_y :
    toLaurentBase K f (y K f) = AdjoinRoot.root (laurentEquation K f) := by
  simp [toLaurentBase, y]

def toLaurent : Overlap K f →ₐ[K] LaurentChart K f :=
  IsLocalization.Away.liftAlgHom (x K f) (by
    rw [toLaurentBase_x]
    exact (LaurentPolynomial.isUnit_T (1 : ℤ)).map (AdjoinRoot.of (laurentEquation K f)))

@[simp] theorem toLaurent_algebraMap (a : Chart K f) :
    toLaurent K f (algebraMap (Chart K f) (Overlap K f) a) = toLaurentBase K f a := by
  simp [toLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

theorem coefficient_X_unit : IsUnit
    (((Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) X) := by
  change IsUnit (algebraMap (Chart K f) (Overlap K f) (x K f))
  exact IsLocalization.Away.algebraMap_isUnit (x K f)

def fromLaurentCoefficients : LaurentPolynomial K →ₐ[K] Overlap K f :=
  IsLocalization.Away.liftAlgHom (X : Polynomial K)
    (f := (Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) (coefficient_X_unit K f)

@[simp] theorem fromLaurentCoefficients_toLaurent (p : Polynomial K) :
    fromLaurentCoefficients K f p.toLaurent =
      algebraMap (Chart K f) (Overlap K f) (AdjoinRoot.of (equation K f) p) := by
  change fromLaurentCoefficients K f
    (algebraMap (Polynomial K) (LaurentPolynomial K) p) = _
  exact IsLocalization.Away.lift_eq (X : Polynomial K) (coefficient_X_unit K f) p

def fromLaurent : LaurentChart K f →ₐ[K] Overlap K f :=
  AdjoinRoot.liftAlgHom (laurentEquation K f) (fromLaurentCoefficients K f)
    (algebraMap (Chart K f) (Overlap K f) (y K f)) (by
      have h := AdjoinRoot.eval₂_root (equation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      have hm := congrArg (algebraMap (Chart K f) (Overlap K f)) h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change (algebraMap (Chart K f) (Overlap K f) (y K f)) ^ 2 -
        fromLaurentCoefficients K f f.toLaurent = 0
      rw [fromLaurentCoefficients_toLaurent]
      simpa only [map_sub, map_pow, map_zero, y] using hm)

@[simp] theorem fromLaurent_root :
    fromLaurent K f (AdjoinRoot.root (laurentEquation K f)) =
      algebraMap (Chart K f) (Overlap K f) (y K f) := by
  simp [fromLaurent]

theorem fromLaurent_comp_toLaurent :
    (fromLaurent K f).comp (toLaurent K f) = AlgHom.id K (Overlap K f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x K f))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (x K f))) =
      algebraMap (Chart K f) (Overlap K f) (x K f)
    rw [toLaurent_algebraMap, toLaurentBase_x]
    rw [← Polynomial.toLaurent_X]
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent]
    rfl
  · change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (y K f))) =
      algebraMap (Chart K f) (Overlap K f) (y K f)
    simp

theorem toLaurent_comp_fromLaurent :
    (toLaurent K f).comp (fromLaurent K f) = AlgHom.id K (LaurentChart K f) := by
  apply AdjoinRoot.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : Polynomial K))
    apply Polynomial.algHom_ext
    change toLaurent K f (fromLaurent K f (AdjoinRoot.of (laurentEquation K f)
      (Polynomial.toLaurent X))) = AdjoinRoot.of (laurentEquation K f) (Polynomial.toLaurent X)
    change toLaurent K f (AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _)) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent,
      toLaurent_algebraMap]
    simpa only [x, Polynomial.toLaurent_X] using toLaurentBase_x K f
  · simp

def overlapAlgEquiv : Overlap K f ≃ₐ[K] LaurentChart K f :=
  AlgEquiv.ofAlgHom (toLaurent K f) (fromLaurent K f)
    (toLaurent_comp_fromLaurent K f) (fromLaurent_comp_toLaurent K f)

end MazurTransfer.HyperellipticLaurentOverlap


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: compute the quotient of Laurent coefficient pairs by the
two chart images with transitions x = z^-1 and y = w z^-3.
Named downstream consumer: the actual order-thirteen two-chart Cech quotient.
This algebraic coefficient calculation alone is not a genus theorem.
-/

noncomputable section
namespace MazurTransfer.LaurentTwoChartCoefficientQuotient

variable (K : Type*) [Field K]
abbrev LaurentCoefficients := ℤ →₀ K
abbrev ChartCoefficients := ℕ →₀ K
abbrev OverlapCoefficients := LaurentCoefficients K × LaurentCoefficients K

def ordinary : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ)))

def reciprocal : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ) - 3))

def boundaries : Submodule K (OverlapCoefficients K) := (ordinary K).range ⊔ (reciprocal K).range

def survivingCoefficients : OverlapCoefficients K →ₗ[K] K × K where
  toFun v := (v.2 (-1), v.2 (-2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem range_lmapDomain_eq_supported (e : ℕ → ℤ) :
    (Finsupp.lmapDomain K K e).range = Finsupp.supported K K (Set.range e) := by
  rw [Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single]
  congr 1
  ext z
  simp

theorem ordinary_range : (ordinary K).range =
    (Finsupp.supported K K {n : ℤ | 0 ≤ n}).prod
      (Finsupp.supported K K {n : ℤ | 0 ≤ n}) := by
  rw [ordinary, LinearMap.range_prodMap, range_lmapDomain_eq_supported]
  congr 2 <;> ext z <;> simp

theorem reciprocal_range : (reciprocal K).range =
    (Finsupp.supported K K {n : ℤ | n ≤ 0}).prod
      (Finsupp.supported K K {n : ℤ | n ≤ -3}) := by
  rw [reciprocal, LinearMap.range_prodMap, range_lmapDomain_eq_supported,
    range_lmapDomain_eq_supported]
  have h₀ : Set.range (fun n : ℕ => -(n : ℤ)) = {n : ℤ | n ≤ 0} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ 0 at hz
      refine ⟨(-z).toNat, ?_⟩
      change -((-z).toNat : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  have h₃ : Set.range (fun n : ℕ => -(n : ℤ) - 3) = {n : ℤ | n ≤ -3} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ -3 at hz
      refine ⟨(-z-3).toNat, ?_⟩
      change -((-z-3).toNat : ℤ) - 3 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  rw [h₀, h₃]

theorem boundaries_eq_kernel : boundaries K = (survivingCoefficients K).ker := by
  rw [boundaries, ordinary_range, reciprocal_range]
  apply le_antisymm
  · apply sup_le
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
  · intro v hv
    have hzero : v.2 (-1) = 0 ∧ v.2 (-2) = 0 := by
      change (v.2 (-1), v.2 (-2)) = (0, 0) at hv
      exact Prod.mk.inj hv
    let positive (a : ℤ →₀ K) := a.filter (fun n => 0 ≤ n)
    let negative (a : ℤ →₀ K) := a.filter (fun n => n < 0)
    refine Submodule.mem_sup.mpr ⟨(positive v.1, positive v.2), ?_,
      (negative v.1, negative v.2), ?_, ?_⟩
    · constructor <;> apply (Finsupp.mem_supported' K _).mpr <;>
        intro n hn <;> change ¬ 0 ≤ n at hn <;> simp [positive, hn]
    · constructor
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        simp [negative, show ¬ n < 0 by omega]
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        by_cases hp : 0 ≤ n
        · simp [negative, show ¬ n < 0 by omega]
        · have hn' : n = -1 ∨ n = -2 := by omega
          rcases hn' with rfl | rfl <;> simp [negative, hzero.1, hzero.2]
    · apply Prod.ext <;> ext n <;> by_cases hn : 0 ≤ n <;>
        simp [positive, negative, hn, show n < 0 ↔ ¬ 0 ≤ n by omega]

theorem survivingCoefficients_surjective : Function.Surjective (survivingCoefficients K) := by
  rintro ⟨a, b⟩
  let v : ℤ →₀ K := Finsupp.single (-1) a + Finsupp.single (-2) b
  refine ⟨(0, v), ?_⟩
  change (v (-1), v (-2)) = (a, b)
  simp [v]

def quotientEquiv : (OverlapCoefficients K ⧸ boundaries K) ≃ₗ[K] K × K :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_kernel K)).trans
    ((survivingCoefficients K).quotKerEquivOfSurjective (survivingCoefficients_surjective K))

theorem quotient_finrank : Module.finrank K (OverlapCoefficients K ⧸ boundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

end MazurTransfer.LaurentTwoChartCoefficientQuotient


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the quotient of the actual overlap coordinate algebra by
the sum of the images of the two actual chart algebras.
Named downstream consumer: comparison with genuine structure-sheaf H1.
This file makes no genus claim without that comparison.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCechQuotient
open Polynomial Module
open MazurTorsion.XOneThirteenAffineCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve

variable (K : Type*) [Field K]
abbrev QuadraticLaurentRing := HyperellipticLaurentOverlap.LaurentChart K (sexticPolynomial K)

def overlapAlgEquiv : OrdinaryOverlapRing K ≃ₐ[K] QuadraticLaurentRing K :=
  HyperellipticLaurentOverlap.overlapAlgEquiv K (sexticPolynomial K)

def overlapCoordinates : OrdinaryOverlapRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.OverlapCoefficients K :=
  (overlapAlgEquiv K).toLinearEquiv.trans
    (((QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent).restrictScalars K).trans
      ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K)))

def ordinaryCoordinates : CoordinateRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

def reciprocalCoordinates : ReciprocalRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

theorem overlapCoordinates_of_add_of_mul_root (a b : LaurentPolynomial K) :
    overlapCoordinates K ((overlapAlgEquiv K).symm
      (AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) a +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) b *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)))) = (a.coeff, b.coeff) := by
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      ((overlapAlgEquiv K) ((overlapAlgEquiv K).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      (AdjoinRoot.of (QuadraticCoordinates.equation _ _) a + AdjoinRoot.of (QuadraticCoordinates.equation _ _) b *
        AdjoinRoot.root (QuadraticCoordinates.equation _ _))) = _
  rw [QuadraticCoordinates.coordinates_of_add_of_mul_root]
  rfl

theorem laurent_inverse_coordinate :
    overlapAlgEquiv K (IsLocalization.Away.invSelf (xCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  let o := AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
  have hu : IsUnit (o (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T (1 : ℤ)).map o
  apply hu.mul_left_cancel
  have hx : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (xCoordinate K)) =
      o (LaurentPolynomial.T 1) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.x K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_x K (sexticPolynomial K)
  rw [← hx, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, hx]
  change 1 = o (LaurentPolynomial.T 1) * o (LaurentPolynomial.T (-1))
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp only [Int.reduceAdd, LaurentPolynomial.T_zero, map_one]

theorem reciprocal_z_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  rw [reciprocalToOrdinaryBase_z]
  exact laurent_inverse_coordinate K

theorem reciprocal_w_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (wCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-3)) *
        AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  rw [reciprocalToOrdinaryBase_w]
  change overlapAlgEquiv K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3) = _
  rw [map_mul, map_pow, laurent_inverse_coordinate]
  have hy : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)
  rw [hy, ← map_pow, LaurentPolynomial.T_pow]
  norm_num only
  rw [mul_comm]

theorem invert_toLaurent_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ)) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]

theorem invert_toLaurent_shift_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent * LaurentPolynomial.T (-3)).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ) - 3) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]
      rfl

def actualBoundaries : Submodule K (OrdinaryOverlapRing K) :=
  (Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
    (reciprocalToOrdinaryBase K).toLinearMap.range

theorem ordinary_laurent (p : Polynomial K) :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
      (AdjoinRoot.of (affineEquation K) p)) =
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.toLaurent := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (AdjoinRoot.of (HyperellipticLaurentOverlap.equation K (sexticPolynomial K)) p)) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  simp [HyperellipticLaurentOverlap.toLaurentBase]

theorem ordinary_y_laurent :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)

theorem reciprocal_laurent (p : Polynomial K) :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (AdjoinRoot.of (reciprocalEquation K) p)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.toLaurent) := by
  have h : ((overlapAlgEquiv K).toAlgHom.comp (reciprocalToOrdinaryBase K)).comp
      (AdjoinRoot.ofAlgHom K (reciprocalEquation K)) =
    (AdjoinRoot.ofAlgHom K (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))).comp
      (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) := by
    apply Polynomial.algHom_ext
    change overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert (Polynomial.toLaurent (X : Polynomial K)))
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    exact reciprocal_z_laurent K
  exact DFunLike.congr_fun h p

theorem ordinary_diagram (a : CoordinateRing K) :
    overlapCoordinates K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      LaurentTwoChartCoefficientQuotient.ordinary K (ordinaryCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K) a
  have ha : a = AdjoinRoot.of (affineEquation K) p.1 +
      AdjoinRoot.of (affineEquation K) p.2 * yCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (sexticPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.1.toLaurent +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.2.toLaurent *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, ordinary_laurent, ordinary_laurent,
      ordinary_y_laurent]
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root]
  rfl

theorem reciprocal_diagram (a : ReciprocalRing K) :
    overlapCoordinates K (reciprocalToOrdinaryBase K a) =
      LaurentTwoChartCoefficientQuotient.reciprocal K (reciprocalCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
  have ha : a = AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (reciprocalToOrdinaryBase K a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.1.toLaurent) +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
          (LaurentPolynomial.invert p.2.toLaurent * LaurentPolynomial.T (-3)) *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, reciprocal_laurent, reciprocal_laurent,
      reciprocal_w_laurent, map_mul]
    ring
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root, invert_toLaurent_coeff,
    invert_toLaurent_shift_coeff]
  rfl

theorem actualBoundaries_image :
    (actualBoundaries K).map (overlapCoordinates K).toLinearMap =
      LaurentTwoChartCoefficientQuotient.boundaries K := by
  rw [actualBoundaries, LaurentTwoChartCoefficientQuotient.boundaries, Submodule.map_sup]
  congr 1
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨ordinaryCoordinates K a, (ordinary_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
        ((ordinaryCoordinates K).symm c), ⟨(ordinaryCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) ((ordinaryCoordinates K).symm c)) = _
      rw [ordinary_diagram, LinearEquiv.apply_symm_apply]
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨reciprocalCoordinates K a, (reciprocal_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c),
        ⟨(reciprocalCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c)) = _
      rw [reciprocal_diagram, LinearEquiv.apply_symm_apply]

def quotientEquiv : (OrdinaryOverlapRing K ⧸ actualBoundaries K) ≃ₗ[K] K × K :=
  (Submodule.Quotient.equiv (actualBoundaries K) (LaurentTwoChartCoefficientQuotient.boundaries K)
    (overlapCoordinates K) (actualBoundaries_image K)).trans
      (LaurentTwoChartCoefficientQuotient.quotientEquiv K)

theorem actual_two_chart_section_quotient_finrank :
    Module.finrank K (OrdinaryOverlapRing K ⧸ actualBoundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

def reciprocalPolynomialSections : (Polynomial K × Polynomial K) →ₗ[K] OrdinaryOverlapRing K :=
  let coeff := (Polynomial.aeval (IsLocalization.Away.invSelf (xCoordinate K)) :
    Polynomial K →ₐ[K] OrdinaryOverlapRing K).toLinearMap
  coeff.coprod ((LinearMap.mulRight K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3)).comp coeff)

theorem reciprocal_sections_formula (p : Polynomial K × Polynomial K) :
    reciprocalToOrdinaryBase K
      (AdjoinRoot.of (reciprocalEquation K) p.1 +
        AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K) =
      reciprocalPolynomialSections K p := by
  rw [map_add, map_mul]
  simp only [reciprocalToOrdinaryBase, AdjoinRoot.liftAlgHom_of,
    wCoordinate, AdjoinRoot.liftAlgHom_root]
  rfl

theorem reciprocal_polynomial_sections_range :
    (reciprocalToOrdinaryBase K).toLinearMap.range =
      (reciprocalPolynomialSections K).range := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
    refine ⟨p, ?_⟩
    rw [← reciprocal_sections_formula]
    apply congrArg (reciprocalToOrdinaryBase K)
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a)
  · rintro ⟨p, rfl⟩
    exact ⟨AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K,
      reciprocal_sections_formula K p⟩

theorem actual_quotient_finrank_polynomial_sections :
    Module.finrank K (OrdinaryOverlapRing K ⧸
      ((Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
        (reciprocalPolynomialSections K).range)) = 2 := by
  rw [← reciprocal_polynomial_sections_range]
  exact actual_two_chart_section_quotient_finrank K

end MazurTransfer.Order13ActualCechQuotient


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual structure-sheaf sections and restriction maps of the
original order-thirteen cover. Named downstream consumer: true Cech H1 dimension
and the audited official FLT scheme-to-genus comparison. No genus is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
namespace MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

abbrev sectionsCover := (actualTwoAffineOpenCover K).cover (curveToBase K)
abbrev actualStructureSheafSections := (actualTwoAffineOpenCover K).structureSheafSections (curveToBase K)

theorem overlapToCurve_curveToBase :
    overlapToCurve K ≫ curveToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (OrdinaryOverlapRing K))) := by
  rw [overlapToCurve, Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryOverlapMap ordinaryChartToBase
  rw [← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  exact IsScalarTower.algebraMap_eq K (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)

def ordinarySectionsEquiv :
    (sectionsCover K).A0 ≃ₐ[K] _root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K
    (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (curveToBase K) (ordinaryChartMap K)
    (ordinaryOpen K) rfl (ordinaryChartMap_curveToBase K)

def reciprocalSectionsEquiv :
    (sectionsCover K).A1 ≃ₐ[K] ReciprocalRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K (ReciprocalRing K)
    (curveToBase K) (reciprocalChartMap K) (reciprocalOpen K) rfl (reciprocalChartMap_curveToBase K)

def overlapSectionsEquiv :
    (sectionsCover K).A01 ≃ₐ[K] OrdinaryOverlapRing K :=
  MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt K (OrdinaryOverlapRing K)
    (curveToBase K) (overlapToCurve K) (ordinaryOpen K ⊓ reciprocalOpen K)
    (overlap_opensRange K) (overlapToCurve_curveToBase K)

theorem ordinarySections_restrict (z : (sectionsCover K).A0) :
    overlapSectionsEquiv K ((sectionsCover K).ρ0 z) =
      algebraMap (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)
        (ordinarySectionsEquiv K z) := by
  exact MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt_restriction K
    (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (curveToBase K) (ordinaryChartMap K)
    (Algebra.algHom K (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K))
    (overlapToCurve K) (ordinaryChartMap_curveToBase K) (overlapToCurve_curveToBase K)
    rfl (ordinaryOpen K) (ordinaryOpen K ⊓ reciprocalOpen K) rfl (overlap_opensRange K)
    inf_le_left z

theorem reciprocalSections_restrict (z : (sectionsCover K).A1) :
    overlapSectionsEquiv K ((sectionsCover K).ρ1 z) =
      reciprocalToOrdinaryBase K (reciprocalSectionsEquiv K z) := by
  exact MazurTransfer.AffineOpenCoordinateSections.sectionsAlgEquivAt_restriction K
    (ReciprocalRing K) (curveToBase K) (reciprocalChartMap K)
    (reciprocalToOrdinaryBase K) (overlapToCurve K) (reciprocalChartMap_curveToBase K)
    (overlapToCurve_curveToBase K) (overlapToCurve_eq_reciprocal K).symm
    (reciprocalOpen K) (ordinaryOpen K ⊓ reciprocalOpen K) rfl (overlap_opensRange K)
    inf_le_right z

end MazurTorsion.XOneThirteenProjectiveCurve

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual structure-sheaf Cech H1 for the unchanged scheme's
true two-affine-open cover. Named downstream consumer: the official FLT genus
comparison. No derived-cohomology comparison or genus theorem is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
namespace MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
open MazurTransfer.Order13ActualCechQuotient

def coordinateCechDiff :
    (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K × ReciprocalRing K) →ₗ[K] OrdinaryOverlapRing K :=
  (-(Algebra.algHom K (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap).coprod
    (reciprocalToOrdinaryBase K).toLinearMap

theorem coordinateCechDiff_range : (coordinateCechDiff K).range = actualBoundaries K := by
  rw [coordinateCechDiff, LinearMap.range_coprod, LinearMap.range_neg]
  rfl

def chartSectionPairEquiv :
    ((actualStructureSheafSections K).M0 × (actualStructureSheafSections K).M1) ≃ₗ[K]
      (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K × ReciprocalRing K) :=
  (ordinarySectionsEquiv K).toLinearEquiv.prodCongr (reciprocalSectionsEquiv K).toLinearEquiv

theorem cechDiff_section_comparison
    (z : (actualStructureSheafSections K).M0 × (actualStructureSheafSections K).M1) :
    overlapSectionsEquiv K ((actualStructureSheafSections K).cechDiff z) =
      coordinateCechDiff K (chartSectionPairEquiv K z) := by
  rw [TwoChartCech.Sections.cechDiff_apply, map_sub]
  change overlapSectionsEquiv K (((1 : (sectionsCover K).A01ˣ) : (sectionsCover K).A01) *
    (sectionsCover K).ρ1 z.2) -
    overlapSectionsEquiv K ((sectionsCover K).ρ0 z.1) = _
  rw [Units.val_one, one_mul, reciprocalSections_restrict, ordinarySections_restrict]
  simp [coordinateCechDiff, chartSectionPairEquiv, sub_eq_add_neg, add_comm]
  rfl

theorem cechDiff_range_section_comparison :
    Submodule.map (overlapSectionsEquiv K).toLinearEquiv.toLinearMap
      (actualStructureSheafSections K).cechDiff.range = actualBoundaries K := by
  rw [← coordinateCechDiff_range K]
  ext y
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨chartSectionPairEquiv K z, (cechDiff_section_comparison K z).symm⟩
  · rintro ⟨z, rfl⟩
    let w := (chartSectionPairEquiv K).symm z
    refine ⟨(actualStructureSheafSections K).cechDiff w, ⟨w, rfl⟩, ?_⟩
    change overlapSectionsEquiv K ((actualStructureSheafSections K).cechDiff w) = _
    rw [cechDiff_section_comparison, LinearEquiv.apply_symm_apply]

def actualStructureSheafH1Equiv :
    (actualStructureSheafSections K).H1 ≃ₗ[K] (OrdinaryOverlapRing K ⧸ actualBoundaries K) :=
  Submodule.Quotient.equiv _ _ (overlapSectionsEquiv K).toLinearEquiv
    (cechDiff_range_section_comparison K)

theorem actual_structureSheaf_cechH1_finrank :
    Module.finrank K (actualStructureSheafSections K).H1 = 2 := by
  rw [(actualStructureSheafH1Equiv K).finrank_eq]
  exact actual_two_chart_section_quotient_finrank K

end MazurTorsion.XOneThirteenProjectiveCurve

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

theorem actual_cover_open_nonempty (U V : (curveScheme K).Opens)
    (hUV : U ⊔ V = ⊤) (hV : IsAffineOpen V) : Nonempty U := by
  have hUne : (U : Set (curveScheme K)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := TopologicalSpace.Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact actual_affineOpen_ne_top K V hV hUV
  exact hUne.to_subtype

abbrev actualPlaceCechH1 : Type u :=
  cechH1 (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0)
    (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1)
    (0 : Divisor K (actualCurveFunctionField K))

theorem actual_structureSheaf_placeCechH1_equiv :
    Nonempty ((actualStructureSheafSections K).H1 ≃ₗ[K] actualPlaceCechH1 K) := by
  have h0 := actual_cover_open_nonempty K _ _
    (actualTwoAffineOpenCover K).sup_eq_top
    (actualTwoAffineOpenCover K).isAffineOpen_U1
  have h1 := actual_cover_open_nonempty K _ _
    ((sup_comm _ _).trans (actualTwoAffineOpenCover K).sup_eq_top)
    (actualTwoAffineOpenCover K).isAffineOpen_U0
  exact (_root_.AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1
    (actualTwoAffineOpenCover K) (curveToBase K) h0 h1).2

theorem actual_placeCechH1_finrank : Module.finrank K (actualPlaceCechH1 K) = 2 := by
  obtain ⟨e⟩ := actual_structureSheaf_placeCechH1_equiv K
  exact e.finrank_eq.symm.trans (actual_structureSheaf_cechH1_finrank K)

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

theorem actual_globalH1_finrank_of_genusReached
    [IsCurveOver K (actualCurveFunctionField K)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K (actualCurveFunctionField K)))]
    {γ : ℤ} {D₀ : Divisor K (actualCurveFunctionField K)}
    (h : RiemannGenusReachedAt γ D₀) :
    Module.finrank K (H1 (0 : Divisor K (actualCurveFunctionField K))) = 2 := by
  obtain ⟨hcover, h₀, h₁⟩ := actual_places_cover_nonempty_complements K
  let e : actualPlaceCechH1 K ≃ₗ[K] H1 (0 : Divisor K (actualCurveFunctionField K)) :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover 0)
      (cechH1ToH1_bijective h hcover h₀ h₁ 0)
  exact e.finrank_eq.symm.trans (actual_placeCechH1_finrank K)

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

instance actualFunctionFieldEssFiniteType :
    Algebra.EssFiniteType K (actualCurveFunctionField K) :=
  _root_.AlgebraicCurve.essFiniteType_functionField (curveToBase K)

def actualZeroOneAffineHom : _root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K :=
  _root_.MazurTorsion.XOneThirteenAffineCurve.solutionToAlgHom K
    ⟨(0, 1), by simp [_root_.MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial]⟩

def actualZeroOneSection : Spec (.of K) ⟶ curveScheme K :=
  Spec.map (CommRingCat.ofHom (actualZeroOneAffineHom K).toRingHom) ≫ ordinaryChartMap K

theorem actualZeroOneSection_over_base :
    actualZeroOneSection K ≫ curveToBase K = 𝟙 _ := by
  unfold actualZeroOneSection
  rw [Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap K (_root_.MazurTorsion.XOneThirteenAffineCurve.CoordinateRing K)) ≫
      CommRingCat.ofHom (actualZeroOneAffineHom K).toRingHom = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext k
    exact (actualZeroOneAffineHom K).commutes k
  rw [h, Spec.map_id]

theorem actualZeroOnePoint_isClosed :
    IsClosed ({(actualZeroOneSection K).base (IsLocalRing.closedPoint K)} : Set (curveScheme K)) := by
  haveI : IsClosedImmersion (actualZeroOneSection K ≫ curveToBase K) := by
    rw [actualZeroOneSection_over_base]
    infer_instance
  haveI : IsClosedImmersion (actualZeroOneSection K) :=
    IsClosedImmersion.of_comp (actualZeroOneSection K) (curveToBase K)
  have h := (actualZeroOneSection K).isClosedEmbedding.isClosedMap
    {IsLocalRing.closedPoint K} isClosed_singleton
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨IsLocalRing.closedPoint K, Set.mem_singleton _, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).symm
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact Set.mem_singleton _

def actualZeroOneClosedPoint : closedPoints (curveScheme K) :=
  ⟨(actualZeroOneSection K).base (IsLocalRing.closedPoint K),
    mem_closedPoints_iff.mpr (actualZeroOnePoint_isClosed K)⟩

def actualZeroOnePlace : Place K (actualCurveFunctionField K) :=
  actualPlaceOfPoint K (actualZeroOneClosedPoint K)

theorem actualZeroOnePlace_isRational : (actualZeroOnePlace K).IsRational :=
  Place.isRational_of_range_stalk_section_eq (curveToBase K)
    (actualZeroOneSection K) (actualZeroOneSection_over_base K)
    (actualZeroOnePlace K) (actualPlaceOfPoint_stalk_range K (actualZeroOneClosedPoint K))

theorem actualZeroOnePlace_deg : (actualZeroOnePlace K).deg = 1 :=
  ((actualZeroOnePlace K).isRational_iff_deg_eq_one).mp (actualZeroOnePlace_isRational K)

theorem actual_constantsAreBase_good_characteristic : ConstantsAreBase K (actualCurveFunctionField K) :=
  constantsAreBase_of_deg_eq_one (actualZeroOnePlace K) (actualZeroOnePlace_deg K)

theorem actual_stichtenothGenusExists_good_characteristic :
    StichtenothGenusExists K (actualCurveFunctionField K) :=
  stichtenothGenusExists_of_isCurveOver (actual_constantsAreBase_good_characteristic K)

theorem actual_genusFF_eq_two_good_characteristic : genusFF K (actualCurveFunctionField K) = 2 := by
  obtain ⟨_, hfinite, γ, D₀, hgenus⟩ := actual_stichtenothGenusExists_good_characteristic K
  letI := hfinite
  exact actual_globalH1_finrank_of_genusReached K hgenus

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end

end Order13FunctionFieldPublicProof

open AlgebraicGeometry AlgebraicCurve CategoryTheory
open Order13FunctionFieldPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel

theorem solution.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).1
    letI : Algebra K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField :=
      (baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
    IsCurveOver K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      Algebra.EssFiniteType K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      ConstantsAreBase K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField ∧
      genusFF K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField = 2 ∧
      Nonempty (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover := by
  letI : Fact ((104 : K) ≠ 0) := ⟨h104⟩
  exact ⟨actualFunctionFieldIsCurveOver K, actualFunctionFieldEssFiniteType K,
    actual_constantsAreBase_good_characteristic K, actual_genusFF_eq_two_good_characteristic K,
    ⟨Order13FunctionFieldPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K⟩⟩

#print axioms solution
