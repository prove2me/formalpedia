-- Prove2me | solution 1 for MazurTransfer.order13_actual_finite_field_effective_degree_two_divisor_counts
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T13:57:38.331224+00:00
-- url     : https://prove2.me/submissions/2a9bc06f-52b0-461d-8a88-16e3a0862ebd

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_MazurTransfer_Order13DegreeTwoClosedPoints
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_degree_two_closed_point_counts
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
open AlgebraicGeometry AlgebraicCurve CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 3) (by decide)).1
noncomputable local instance : Algebra (ZMod 3) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))).toAlgebra
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 (ZMod 5) (by decide)).1
noncomputable local instance : Algebra (ZMod 5) (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField :=
  (AlgebraicCurve.baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))).toAlgebra

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: base-to-function-field constants agree with constants at
any stalk. Named downstream consumer: public scheme-to-place residue-field
scalar compatibility. The complete mathematical lemma below is selected
unchanged from official Anthropic FLT at pin
6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0 attribution retained.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry _root_.AlgebraicCurve
namespace EffectiveDegreeTwoDivisorProof.FunctionFieldBaseStalkCompatibility
universe u
theorem AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
    (x : C) (a : K) :
    baseToFunctionField c a =
      algebraMap (C.presheaf.stalk x) C.functionField
        ((C.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) := by
  have key : ∀ s : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom s =
      algebraMap (C.presheaf.stalk x) C.functionField ((C.presheaf.germ ⊤ x trivial).hom s) := by
    intro s
    simp_rw [RingHom.algebraMap_toAlgebra]
    change _ = (C.presheaf.germ ⊤ x trivial ≫ C.presheaf.stalkSpecializes _).hom s
    have H := TopCat.Presheaf.germ_stalkSpecializes C.presheaf
      (U := ⊤) (y := x) trivial ((genericPoint_spec C).specializes trivial)
    exact (congrArg (fun f => f.hom s) H).symm
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  exact key _


end EffectiveDegreeTwoDivisorProof.FunctionFieldBaseStalkCompatibility
#print axioms EffectiveDegreeTwoDivisorProof.FunctionFieldBaseStalkCompatibility.AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk

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
namespace EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) := (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).1

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.1

instance actualCurve_isProper : IsProper (curveToBase K) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.2.1

instance actualCurve_isNoetherian : IsNoetherian (curveScheme K) :=
  (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.2.2

instance actualCurve_isSmooth : Smooth (curveToBase K) :=
  SmoothOfRelativeDimension.smooth 1 _

abbrev actualCurveFunctionField : Type u := (curveScheme K).functionField

instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

def actualPlaceOfPoint (x : closedPoints (curveScheme K)) : Place K (actualCurveFunctionField K) :=
  Classical.choose (AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_stalk_range (x : closedPoints (curveScheme K)) :
    (algebraMap ((curveScheme K).presheaf.stalk x.1) (actualCurveFunctionField K)).range =
      (actualPlaceOfPoint K x).toValuationSubring.toSubring :=
  Classical.choose_spec (AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_bijective : Function.Bijective (actualPlaceOfPoint K) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact AlgebraicCurve.eq_of_range_stalk_eq (curveToBase K) x.1 y.1
      (by rw [actualPlaceOfPoint_stalk_range, actualPlaceOfPoint_stalk_range, hxy])
  · intro v
    obtain ⟨x, hx, hrange⟩ :=
      AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase K) v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]

end EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces
#print axioms EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces.actualPlaceOfPoint_bijective

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
namespace EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

instance actualFunctionFieldIsCurveOver : IsCurveOver K (actualCurveFunctionField K) :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (curveToBase K) (RingEquiv.refl _) (fun _ => rfl)

end EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces
#print axioms EffectiveDegreeTwoDivisorProof.Order13ArithmeticPlaces.actualFunctionFieldIsCurveOver

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the scheme residue field and the function-field place
residue field are equivalent over the actual base whenever the stalk range
is the place's valuation ring. Named downstream consumer: transfer the
literal F3/F5 closed-point degrees to genuine FLT place degrees and divisors.
The stalk-range identity is supplied by the checked actual CurveModel.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace EffectiveDegreeTwoDivisorProof.SchemePlaceResidueFields
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
variable (c : X ⟶ Spec (.of K))
abbrev baseFunctionFieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra

def baseStalkMap (x : X) : K →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

def stalkToValuationRingEquiv (x : X) :
    letI := baseFunctionFieldAlgebra c
    ∀ (v : Place K X.functionField),
      (algebraMap (X.presheaf.stalk x) X.functionField).range = v.toValuationSubring.toSubring →
      X.presheaf.stalk x ≃+* v.toValuationSubring := by
  letI := baseFunctionFieldAlgebra c
  intro v hv
  let φ := algebraMap (X.presheaf.stalk x) X.functionField
  let ψ := φ.codRestrict v.toValuationSubring.toSubring (by
    intro a
    rw [← hv]
    exact ⟨a, rfl⟩)
  exact RingEquiv.ofBijective ψ ⟨fun a b hab =>
    IsFractionRing.injective (X.presheaf.stalk x) X.functionField (congrArg Subtype.val hab), by
      intro y
      have hy : (y : X.functionField) ∈ φ.range := by rw [hv]; exact y.2
      obtain ⟨a, ha⟩ := hy
      exact ⟨a, Subtype.ext ha⟩⟩

theorem stalkToValuationRingEquiv_base (x : X) :
    letI := baseFunctionFieldAlgebra c
    ∀ (v : Place K X.functionField)
      (hv : (algebraMap (X.presheaf.stalk x) X.functionField).range = v.toValuationSubring.toSubring)
      (a : K), stalkToValuationRingEquiv c x v hv (baseStalkMap c x a) =
        algebraMap K v.toValuationSubring a := by
  letI := baseFunctionFieldAlgebra c
  intro v hv a
  apply Subtype.ext
  exact (EffectiveDegreeTwoDivisorProof.FunctionFieldBaseStalkCompatibility.AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk c x a).symm

def schemePlaceResidueFieldAlgEquiv (x : X) :
    letI := baseFunctionFieldAlgebra c
    ∀ (v : Place K X.functionField),
      (algebraMap (X.presheaf.stalk x) X.functionField).range = v.toValuationSubring.toSubring →
      letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra c x
      X.residueField x ≃ₐ[K] v.ResidueField := by
  letI := baseFunctionFieldAlgebra c
  intro v hv
  letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra c x
  refine AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv
    (stalkToValuationRingEquiv c x v hv)) ?_
  intro a
  change IsLocalRing.ResidueField.mapEquiv (stalkToValuationRingEquiv c x v hv)
    (IsLocalRing.residue (X.presheaf.stalk x) (baseStalkMap c x a)) =
      IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring a)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue v.toValuationSubring)
    (stalkToValuationRingEquiv_base c x v hv a)

theorem place_degree_eq_geometric_residue_degree (x : X) :
    letI := baseFunctionFieldAlgebra c
    ∀ (v : Place K X.functionField),
      (algebraMap (X.presheaf.stalk x) X.functionField).range = v.toValuationSubring.toSubring →
      letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra c x
      v.deg = Module.finrank K (X.residueField x) := by
  letI := baseFunctionFieldAlgebra c
  intro v hv
  letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra c x
  exact (schemePlaceResidueFieldAlgEquiv c x v hv).toLinearEquiv.finrank_eq.symm

end EffectiveDegreeTwoDivisorProof.SchemePlaceResidueFields
#print axioms EffectiveDegreeTwoDivisorProof.SchemePlaceResidueFields.schemePlaceResidueFieldAlgEquiv
#print axioms EffectiveDegreeTwoDivisorProof.SchemePlaceResidueFields.place_degree_eq_geometric_residue_degree

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine function-field places have the same degrees as
their corresponding geometric closed points on the literal curve.
Named downstream consumer: actual effective degree-two divisor enumeration
and finite-field Picard cardinality. The place-to-point bijection is the
checked complete CurveModel, not a supplied labeling or cardinality.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
namespace EffectiveDegreeTwoDivisorProof.Order13QuadraticPlaceDegrees
open Order13ArithmeticPlaces _root_.MazurTransfer.Order13FiniteCurvePlaces SchemePlaceResidueFields
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

def actualPointPlaceResidueFieldEquiv (x : closedPoints (curveScheme K)) :
    letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra (curveToBase K) x.1
    (curveScheme K).residueField x.1 ≃ₐ[K] (actualPlaceOfPoint K x).ResidueField :=
  schemePlaceResidueFieldAlgEquiv (curveToBase K) x.1 (actualPlaceOfPoint K x)
    (actualPlaceOfPoint_stalk_range K x)

theorem actualPlaceOfPoint_degree (x : closedPoints (curveScheme K)) :
    letI := _root_.MazurTransfer.StructureResidueFields.baseAlgebra (curveToBase K) x.1
    (actualPlaceOfPoint K x).deg = Module.finrank K ((curveScheme K).residueField x.1) :=
  place_degree_eq_geometric_residue_degree (curveToBase K) x.1 (actualPlaceOfPoint K x)
    (actualPlaceOfPoint_stalk_range K x)

def degreeTwoClosedPointsEquivGeometricPoints :
    {x : closedPoints (curveScheme K) // (actualPlaceOfPoint K x).deg = 2} ≃
      {x : curveScheme K // DegreeTwoPoint K x} where
  toFun x := ⟨x.1.1, ⟨mem_closedPoints_iff.mp x.1.2,
    (actualPlaceOfPoint_degree K x.1).symm.trans x.2⟩⟩
  invFun x := ⟨⟨x.1, mem_closedPoints_iff.mpr x.2.1⟩,
    (actualPlaceOfPoint_degree K ⟨x.1, mem_closedPoints_iff.mpr x.2.1⟩).trans x.2.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

def degreeTwoPlacesEquivGeometricPoints :
    {v : Place K (actualCurveFunctionField K) // v.deg = 2} ≃
      {x : curveScheme K // DegreeTwoPoint K x} := by
  let e : closedPoints (curveScheme K) ≃ Place K (actualCurveFunctionField K) :=
    Equiv.ofBijective (actualPlaceOfPoint K) (actualPlaceOfPoint_bijective K)
  let e₂ : {x : closedPoints (curveScheme K) // (e x).deg = 2} ≃
      {v : Place K (actualCurveFunctionField K) // v.deg = 2} :=
    Equiv.subtypeEquivOfSubtype (p := fun v : Place K (actualCurveFunctionField K) => v.deg = 2) e
  exact e₂.symm.trans (degreeTwoClosedPointsEquivGeometricPoints K)

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 3) ≠ 0) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 5) ≠ 0) := ⟨by decide⟩

theorem actualDegreeTwoPlacesThree_card :
    Nat.card {v : Place (ZMod 3) (actualCurveFunctionField (ZMod 3)) // v.deg = 2} = 1 := by
  rw [Nat.card_congr (degreeTwoPlacesEquivGeometricPoints (ZMod 3))]
  exact MazurTransfer.order13_actual_degree_two_closed_point_counts.1

theorem actualDegreeTwoPlacesFive_card :
    Nat.card {v : Place (ZMod 5) (actualCurveFunctionField (ZMod 5)) // v.deg = 2} = 3 := by
  rw [Nat.card_congr (degreeTwoPlacesEquivGeometricPoints (ZMod 5))]
  exact MazurTransfer.order13_actual_degree_two_closed_point_counts.2

end EffectiveDegreeTwoDivisorProof.Order13QuadraticPlaceDegrees
#print axioms EffectiveDegreeTwoDivisorProof.Order13QuadraticPlaceDegrees.actualPointPlaceResidueFieldEquiv
#print axioms EffectiveDegreeTwoDivisorProof.Order13QuadraticPlaceDegrees.actualDegreeTwoPlacesThree_card
#print axioms EffectiveDegreeTwoDivisorProof.Order13QuadraticPlaceDegrees.actualDegreeTwoPlacesFive_card

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: lift a curve point to a section over an isomorphic residue
field while preserving the actual base morphism. Named downstream consumer:
exhausting all degree-two places using the F9/F25 point dictionary.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EffectiveDegreeTwoDivisorProof.ResidueFieldPointLifts
open _root_.MazurTransfer.StructureResidueFields NeronModelInfra
universe u

theorem fromSpecResidueField_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ = Spec.map (X.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

theorem fromSpecResidueField_over_base {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (x : X) :
    X.fromSpecResidueField x ≫ c = Spec.map (baseRingMap c x) := by
  apply (cancel_mono (Spec (.of R)).toSpecΓ).mp
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
    fromSpecResidueField_toSpecΓ, ← Spec.map_comp,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  apply Spec.map_inj.mpr
  simp [baseRingMap]

def sectionFromResidueFieldEquiv {R K : Type u} [Field R] [Field K] [Algebra R K]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (x : X)
    (e : letI := baseAlgebra c x; X.residueField x ≃ₐ[R] K) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) c := by
  letI := baseAlgebra c x
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, fromSpecResidueField_over_base, ← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext r
  exact e.commutes r

theorem sectionFromResidueFieldEquiv_image {R K : Type u} [Field R] [Field K] [Algebra R K]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (x : X)
    (e : letI := baseAlgebra c x; X.residueField x ≃ₐ[R] K) :
    (sectionFromResidueFieldEquiv c x e).1 (IsLocalRing.closedPoint K) = x := by
  letI := baseAlgebra c x
  change X.fromSpecResidueField x
    ((Spec.map (CommRingCat.ofHom e.toRingHom)) (IsLocalRing.closedPoint K)) = x
  exact Scheme.fromSpecResidueField_apply x _

end EffectiveDegreeTwoDivisorProof.ResidueFieldPointLifts
#print axioms EffectiveDegreeTwoDivisorProof.ResidueFieldPointLifts.fromSpecResidueField_over_base
#print axioms EffectiveDegreeTwoDivisorProof.ResidueFieldPointLifts.sectionFromResidueFieldEquiv
#print axioms EffectiveDegreeTwoDivisorProof.ResidueFieldPointLifts.sectionFromResidueFieldEquiv_image

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: residue degree one of actual rational sections, with the
unchanged generic base-scalar and residue-field equivalence proofs isolated.
Named downstream consumer: public exhaustive degree-one place counts.
No quadratic-field construction is required by this interface.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace EffectiveDegreeTwoDivisorProof.RationalResidueFieldPointDegrees
open _root_.MazurTransfer.StructureResidueFields ResidueFieldPointLifts NeronModelInfra
universe u
local instance (R : Type u) [Field R] (x : Spec (.of R)) : x.asIdeal.IsPrime := x.isPrime

theorem selfBaseMap_eq_id (R : Type u) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (.of R)) := by
  change Spec.map (𝟙 (CommRingCat.of R)) = _
  exact Spec.map_id _

def specResidueFieldEquivBase (R : Type u) [Field R] (x : Spec (.of R)) :
    letI := baseAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R R))) x
    (Spec (.of R)).residueField x ≃ₐ[R] R := by
  letI := baseAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R R))) x
  exact (idealToSpecResidueFieldAlgEquiv (R := R) x).symm.trans
    (Ideal.algEquivResidueFieldOfField x.asIdeal).symm

def rationalSectionResidueFieldEquiv {R : Type u} [Field R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (p : SchemeHomOver (𝟙 (Spec (.of R))) c) :
    letI := baseAlgebra c (p.1 (IsLocalRing.closedPoint R))
    X.residueField (p.1 (IsLocalRing.closedPoint R)) ≃ₐ[R] R := by
  let x0 : Spec (.of R) := IsLocalRing.closedPoint R
  let cR := Spec.map (CommRingCat.ofHom (algebraMap R R))
  letI := baseAlgebra c (p.1 x0)
  letI := baseAlgebra cR x0
  have hp : p.1 ≫ c = cR := p.2.trans (selfBaseMap_eq_id R).symm
  let φ : X.residueField (p.1 x0) →ₐ[R] R :=
    (specResidueFieldEquivBase R x0).toAlgHom.comp (residueFieldAlgHom cR c p.1 hp x0)
  exact AlgEquiv.ofBijective φ ⟨RingHom.injective _, by
    intro r
    exact ⟨algebraMap R (X.residueField (p.1 x0)) r, φ.commutes r⟩⟩

theorem rationalSectionResidueField_degree {R : Type u} [Field R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (p : SchemeHomOver (𝟙 (Spec (.of R))) c) :
    letI := baseAlgebra c (p.1 (IsLocalRing.closedPoint R))
    Module.finrank R (X.residueField (p.1 (IsLocalRing.closedPoint R))) = 1 := by
  letI := baseAlgebra c (p.1 (IsLocalRing.closedPoint R))
  rw [(rationalSectionResidueFieldEquiv c p).toLinearEquiv.finrank_eq]
  exact Module.finrank_self R


end EffectiveDegreeTwoDivisorProof.RationalResidueFieldPointDegrees
#print axioms EffectiveDegreeTwoDivisorProof.RationalResidueFieldPointDegrees.rationalSectionResidueField_degree

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: rational sections and all geometric closed points of residue
degree one over a field with a unique ring endomorphism, including F3 and F5.
Named downstream consumer: actual degree-one place counts and effective
degree-two divisor enumeration. The algebra structure is induced by the
actual scheme-to-base morphism, without a supplied residue-field model.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EffectiveDegreeTwoDivisorProof.DegreeOneCurvePoints
open _root_.MazurTransfer.StructureResidueFields ResidueFieldPointLifts RationalResidueFieldPointDegrees
universe u
variable {R : Type u} [Field R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

abbrev RationalSection := NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) c

def pointOfSection (p : RationalSection c) : X := p.1 (IsLocalRing.closedPoint R)

def DegreeOnePoint (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧
    letI := baseAlgebra c x
    Module.finrank R (X.residueField x) = 1

theorem sectionPoint_isClosed (p : RationalSection c) :
    IsClosed ({pointOfSection c p} : Set X) := by
  let : IsClosedImmersion p.1 := isClosedImmersion_of_comp_eq_id c p.1 p.2
  have h := p.1.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint R} isClosed_singleton
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨IsLocalRing.closedPoint R, Set.mem_singleton _, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).symm
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact Set.mem_singleton _

theorem sectionPoint_degreeOne (p : RationalSection c) : DegreeOnePoint c (pointOfSection c p) :=
  ⟨sectionPoint_isClosed c p, rationalSectionResidueField_degree c p⟩

theorem ringHom_unique_of_equiv [Subsingleton (R →+* R)]
    {A : Type u} [CommRing A] (e : A ≃+* R) (f g : A →+* R) : f = g := by
  have h : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := Subsingleton.elim _ _
  ext a
  have ha := DFunLike.congr_fun h (e a)
  simpa using ha

theorem pointOfSection_injective [Subsingleton (R →+* R)] :
    Function.Injective (pointOfSection c) := by
  intro p q h
  letI := baseAlgebra c (p.1 (IsLocalRing.closedPoint R))
  apply Subtype.ext
  apply (Scheme.SpecToEquivOfField R X).injective
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨h, ?_⟩
  apply CommRingCat.hom_ext
  exact ringHom_unique_of_equiv (rationalSectionResidueFieldEquiv c p).toRingEquiv _ _

def residueFieldEquivBaseOfDegreeOne (x : X) :
    letI := baseAlgebra c x
    Module.finrank R (X.residueField x) = 1 → X.residueField x ≃ₐ[R] R := by
  letI := baseAlgebra c x
  intro h
  exact (AlgEquiv.ofBijective (Algebra.ofId R (X.residueField x))
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)).symm

theorem degreeOnePoint_in_image (x : X) (hx : DegreeOnePoint c x) :
    ∃ p : RationalSection c, pointOfSection c p = x := by
  letI := baseAlgebra c x
  let e := residueFieldEquivBaseOfDegreeOne c x hx.2
  let s := sectionFromResidueFieldEquiv c x e
  let p : RationalSection c := ⟨s.1, s.2.trans (selfBaseMap_eq_id R)⟩
  exact ⟨p, sectionFromResidueFieldEquiv_image c x e⟩

def rationalSectionEquivDegreeOnePoints [Subsingleton (R →+* R)] :
    RationalSection c ≃ {x : X // DegreeOnePoint c x} := by
  let g : RationalSection c → {x : X // DegreeOnePoint c x} :=
    fun p => ⟨pointOfSection c p, sectionPoint_degreeOne c p⟩
  exact Equiv.ofBijective g ⟨by
    intro p q h
    exact pointOfSection_injective c (congrArg Subtype.val h), by
      intro x
      obtain ⟨p, hp⟩ := degreeOnePoint_in_image c x.1 x.2
      exact ⟨p, Subtype.ext hp⟩⟩

end EffectiveDegreeTwoDivisorProof.DegreeOneCurvePoints
#print axioms EffectiveDegreeTwoDivisorProof.DegreeOneCurvePoints.pointOfSection_injective
#print axioms EffectiveDegreeTwoDivisorProof.DegreeOneCurvePoints.rationalSectionEquivDegreeOnePoints

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: all genuine degree-one places of the actual F3/F5 function
fields correspond to actual rational sections and have cardinality six.
Named downstream consumer: enumeration of effective divisors of degree two.
No abstract curve, transported finite group or supplied place model is used.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
namespace EffectiveDegreeTwoDivisorProof.Order13RationalPlaceCounts
open Order13ArithmeticPlaces Order13QuadraticPlaceDegrees DegreeOneCurvePoints
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

def degreeOneClosedPointsEquivGeometricPoints :
    {x : closedPoints (curveScheme K) // (actualPlaceOfPoint K x).deg = 1} ≃
      {x : curveScheme K // DegreeOnePoint (curveToBase K) x} where
  toFun x := ⟨x.1.1, ⟨mem_closedPoints_iff.mp x.1.2,
    (actualPlaceOfPoint_degree K x.1).symm.trans x.2⟩⟩
  invFun x := ⟨⟨x.1, mem_closedPoints_iff.mpr x.2.1⟩,
    (actualPlaceOfPoint_degree K ⟨x.1, mem_closedPoints_iff.mpr x.2.1⟩).trans x.2.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

def degreeOnePlacesEquivGeometricPoints :
    {v : Place K (actualCurveFunctionField K) // v.deg = 1} ≃
      {x : curveScheme K // DegreeOnePoint (curveToBase K) x} := by
  let e : closedPoints (curveScheme K) ≃ Place K (actualCurveFunctionField K) :=
    Equiv.ofBijective (actualPlaceOfPoint K) (actualPlaceOfPoint_bijective K)
  let e₁ : {x : closedPoints (curveScheme K) // (e x).deg = 1} ≃
      {v : Place K (actualCurveFunctionField K) // v.deg = 1} :=
    Equiv.subtypeEquivOfSubtype (p := fun v : Place K (actualCurveFunctionField K) => v.deg = 1) e
  exact e₁.symm.trans (degreeOneClosedPointsEquivGeometricPoints K)

def degreeOnePlacesEquivRationalSections [Subsingleton (K →+* K)] :
    {v : Place K (actualCurveFunctionField K) // v.deg = 1} ≃
      RationalSection (curveToBase K) :=
  (degreeOnePlacesEquivGeometricPoints K).trans
    (rationalSectionEquivDegreeOnePoints (curveToBase K)).symm

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 3) ≠ 0) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 5) ≠ 0) := ⟨by decide⟩

theorem actualDegreeOnePlacesThree_card :
    Nat.card {v : Place (ZMod 3) (actualCurveFunctionField (ZMod 3)) // v.deg = 1} = 6 := by
  rw [Nat.card_congr (degreeOnePlacesEquivRationalSections (ZMod 3))]
  exact MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.{0}.2.1

theorem actualDegreeOnePlacesFive_card :
    Nat.card {v : Place (ZMod 5) (actualCurveFunctionField (ZMod 5)) // v.deg = 1} = 6 := by
  rw [Nat.card_congr (degreeOnePlacesEquivRationalSections (ZMod 5))]
  exact MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.{0}.2.2

end EffectiveDegreeTwoDivisorProof.Order13RationalPlaceCounts
#print axioms EffectiveDegreeTwoDivisorProof.Order13RationalPlaceCounts.degreeOnePlacesEquivRationalSections
#print axioms EffectiveDegreeTwoDivisorProof.Order13RationalPlaceCounts.actualDegreeOnePlacesThree_card
#print axioms EffectiveDegreeTwoDivisorProof.Order13RationalPlaceCounts.actualDegreeOnePlacesFive_card

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: enumerate every effective integral divisor of weighted
degree two when every point weight is positive. Named downstream consumer:
the actual F3/F5 function-field divisors, with weights equal to place degrees.
This is a combinatorial bridge; it assumes no Picard class calculation.
-/

noncomputable section
namespace EffectiveDegreeTwoDivisorProof.WeightedEffectiveDegreeTwo
universe u
variable {α : Type u} (d : α → ℕ)
local instance : DecidableEq α := Classical.decEq _

def degree : (α →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun a => AddMonoidHom.mulRight (d a : ℤ)

@[simp] theorem degree_single (a : α) (n : ℤ) :
    degree d (Finsupp.single a n) = n * d a := by simp [degree]

def EffectiveTwo := {D : α →₀ ℤ // (∀ a, 0 ≤ D a) ∧ degree d D = 2}
abbrev Ones := {a : α // d a = 1}
abbrev Twos := {a : α // d a = 2}

def pairDivisor : Sym2 (Ones d) → α →₀ ℤ :=
  Sym2.lift ⟨fun a b => Finsupp.single a.1 1 + Finsupp.single b.1 1,
    fun a b => add_comm (Finsupp.single a.1 1) (Finsupp.single b.1 1)⟩

@[simp] theorem pairDivisor_mk (a b : Ones d) :
    pairDivisor d s(a, b) = Finsupp.single a.1 1 + Finsupp.single b.1 1 := rfl

theorem pairDivisor_effective (p : Sym2 (Ones d)) : ∀ a, 0 ≤ pairDivisor d p a := by
  induction p using Sym2.ind
  intro a
  simp only [pairDivisor_mk, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem pairDivisor_degree (p : Sym2 (Ones d)) : degree d (pairDivisor d p) = 2 := by
  induction p using Sym2.ind with
  | h a b => simp [pairDivisor_mk, degree_single, a.2, b.2]

def enumerate : Sym2 (Ones d) ⊕ Twos d → EffectiveTwo d
  | .inl p => ⟨pairDivisor d p, pairDivisor_effective d p, pairDivisor_degree d p⟩
  | .inr a => ⟨Finsupp.single a.1 1, by
      intro b
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num, by simp [degree_single, a.2]⟩

theorem sum_singles_injective (a b c e : α)
    (h : Finsupp.single a (1 : ℤ) + Finsupp.single b 1 =
      Finsupp.single c 1 + Finsupp.single e 1) :
    (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  have ha : a = c ∨ a = e := by
    by_contra hn
    push Not at hn
    have hh := DFunLike.congr_fun h a
    simp [Finsupp.single_apply, hn.1, hn.2, Ne.symm hn.1, Ne.symm hn.2] at hh
    split_ifs at hh <;> norm_num at hh
  rcases ha with rfl | rfl
  · have hb : b = e := Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0)
      (add_left_cancel h)
    exact Or.inl ⟨rfl, hb⟩
  · have hb : b = c := Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0)
      (add_left_cancel (h.trans (add_comm _ _)))
    exact Or.inr ⟨rfl, hb⟩

theorem pairDivisor_injective : Function.Injective (pairDivisor d) := by
  intro p q h
  induction p using Sym2.ind with
  | h a b =>
    induction q using Sym2.ind with
    | h c e =>
      rcases sum_singles_injective a.1 b.1 c.1 e.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact congrArg₂ Sym2.mk (Subtype.ext ha) (Subtype.ext hb)
      · rw [Sym2.eq_swap]
        exact congrArg₂ Sym2.mk (Subtype.ext hb) (Subtype.ext ha)

theorem pairDivisor_ne_single (p : Sym2 (Ones d)) (a : Twos d) :
    pairDivisor d p ≠ Finsupp.single a.1 1 := by
  induction p using Sym2.ind with
  | h b c =>
    intro heq
    have hab : b.1 ≠ a.1 := by
      intro h
      have he : (1 : ℕ) = 2 := b.2.symm.trans ((congrArg d h).trans a.2)
      omega
    have hac : c.1 ≠ a.1 := by
      intro h
      have he : (1 : ℕ) = 2 := c.2.symm.trans ((congrArg d h).trans a.2)
      omega
    have h := DFunLike.congr_fun heq a.1
    simp [pairDivisor_mk, Finsupp.single_apply, hab, hac, Ne.symm hab, Ne.symm hac] at h

theorem enumerate_injective : Function.Injective (enumerate d) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (pairDivisor_injective d (congrArg Subtype.val h))
    | inr q => exact False.elim (pairDivisor_ne_single d p q (congrArg Subtype.val h))
  | inr p =>
    cases q with
    | inl q => exact False.elim (pairDivisor_ne_single d q p (congrArg Subtype.val h).symm)
    | inr q =>
      exact congrArg Sum.inr (Subtype.ext
        (Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0) (congrArg Subtype.val h)))

theorem effective_support_card_le_two (hd : ∀ a, 0 < d a) (D : EffectiveTwo d) :
    D.1.support.card ≤ 2 := by
  have hterm (a : α) (ha : a ∈ D.1.support) : (1 : ℤ) ≤ D.1 a * d a := by
    have hcoef : 0 < D.1 a := lt_of_le_of_ne (D.2.1 a) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    have hweight : (1 : ℤ) ≤ d a := by exact_mod_cast hd a
    nlinarith
  have hsum : (D.1.support.card : ℤ) ≤ 2 := by
    calc
      _ = ∑ _a ∈ D.1.support, (1 : ℤ) := by simp
      _ ≤ ∑ a ∈ D.1.support, D.1 a * d a := Finset.sum_le_sum hterm
      _ = degree d D.1 := rfl
      _ = 2 := D.2.2
  exact_mod_cast hsum

theorem finsupp_eq_single_of_support {D : α →₀ ℤ} {a : α} (h : D.support = {a}) :
    D = Finsupp.single a (D a) := by
  ext b
  by_cases hb : b = a
  · subst b; simp
  · have hzero : D b = 0 := Finsupp.notMem_support_iff.mp (by simpa [h] using hb)
    simp [Finsupp.single_apply, hb, Ne.symm hb, hzero]

theorem finsupp_eq_pair_of_support {D : α →₀ ℤ} {a b : α} (hab : a ≠ b)
    (h : D.support = {a, b}) : D = Finsupp.single a (D a) + Finsupp.single b (D b) := by
  ext c
  by_cases hca : c = a
  · subst c; simp [hab, Ne.symm hab]
  · by_cases hcb : c = b
    · subst c; simp [hab, Ne.symm hab]
    · have hz : D c = 0 := Finsupp.notMem_support_iff.mp (by simp [h, hca, hcb])
      simp [Finsupp.single_apply, hca, hcb, Ne.symm hca, Ne.symm hcb, hz]

theorem enumerate_surjective (hd : ∀ a, 0 < d a) : Function.Surjective (enumerate d) := by
  intro D
  have hc := effective_support_card_le_two d hd D
  interval_cases hs : D.1.support.card
  · have hzero : D.1 = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hs)
    have hz := D.2.2
    rw [hzero, map_zero] at hz
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hs
    have hD := finsupp_eq_single_of_support ha
    have hcoef : 0 < D.1 a := lt_of_le_of_ne (D.2.1 a)
      (Ne.symm (Finsupp.mem_support_iff.mp (by simp [ha])))
    have hweight : (1 : ℤ) ≤ d a := by exact_mod_cast hd a
    have heq := D.2.2
    rw [hD, degree_single] at heq
    have hwle : d a ≤ 2 := by exact_mod_cast (show (d a : ℤ) ≤ 2 by nlinarith)
    have hcle : D.1 a ≤ 2 := by nlinarith
    have hcases : D.1 a = 1 ∨ D.1 a = 2 := by omega
    rcases hcases with hca | hca
    · have hda : d a = 2 := by rw [hca, one_mul] at heq; exact_mod_cast heq
      refine ⟨.inr ⟨a, hda⟩, Subtype.ext ?_⟩
      change Finsupp.single a (1 : ℤ) = D.1
      simpa [hca] using hD.symm
    · have hda : d a = 1 := by rw [hca] at heq; omega
      refine ⟨.inl s(⟨a, hda⟩, ⟨a, hda⟩), Subtype.ext ?_⟩
      change Finsupp.single a (1 : ℤ) + Finsupp.single a 1 = D.1
      rw [← Finsupp.single_add]
      simpa [hca] using hD.symm
  · obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hs
    have hD := finsupp_eq_pair_of_support hab hsupp
    have hca : 0 < D.1 a := lt_of_le_of_ne (D.2.1 a)
      (Ne.symm (Finsupp.mem_support_iff.mp (by simp [hsupp])))
    have hcb : 0 < D.1 b := lt_of_le_of_ne (D.2.1 b)
      (Ne.symm (Finsupp.mem_support_iff.mp (by simp [hsupp])))
    have hwa : (1 : ℤ) ≤ d a := by exact_mod_cast hd a
    have hwb : (1 : ℤ) ≤ d b := by exact_mod_cast hd b
    have heq := D.2.2
    rw [hD, map_add, degree_single, degree_single] at heq
    have hprodA : D.1 a * d a = 1 := by nlinarith
    have hprodB : D.1 b * d b = 1 := by nlinarith
    have ha1 : D.1 a = 1 := by nlinarith
    have hb1 : D.1 b = 1 := by nlinarith
    have hda : d a = 1 := by rw [ha1, one_mul] at hprodA; exact_mod_cast hprodA
    have hdb : d b = 1 := by rw [hb1, one_mul] at hprodB; exact_mod_cast hprodB
    refine ⟨.inl s(⟨a, hda⟩, ⟨b, hdb⟩), Subtype.ext ?_⟩
    change Finsupp.single a (1 : ℤ) + Finsupp.single b 1 = D.1
    exact (hD.trans (by rw [ha1, hb1])).symm

def enumerationEquiv (hd : ∀ a, 0 < d a) : Sym2 (Ones d) ⊕ Twos d ≃ EffectiveTwo d :=
  Equiv.ofBijective (enumerate d) ⟨enumerate_injective d, enumerate_surjective d hd⟩

end EffectiveDegreeTwoDivisorProof.WeightedEffectiveDegreeTwo
#print axioms EffectiveDegreeTwoDivisorProof.WeightedEffectiveDegreeTwo.enumerationEquiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: all effective degree-two divisors on the genuine function
fields of the literal F3/F5 curves have cardinalities twenty-two and twenty-four.
Named downstream consumer: canonical-pencil class fibres and actual Picard
cardinality. These are actual integral divisors on actual function-field
places; no transported nineteen-element group or Picard count is assumed.
-/

noncomputable section
open AlgebraicCurve
namespace EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts
open Order13ArithmeticPlaces Order13RationalPlaceCounts Order13QuadraticPlaceDegrees
universe u

abbrev EffectiveDegreeTwo (K F : Type u) [Field K] [Field F] [Algebra K F] :=
  {D : Divisor K F // (∀ v, 0 ≤ D v) ∧ Divisor.degree D = 2}

theorem place_degree_pos {K F : Type u} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] (v : Place K F) : 0 < v.deg := by
  let : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  exact Module.finrank_pos

theorem effective_degree_two_card_of_place_counts {K F : Type u}
    [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (m : ℕ) (hm : 0 < m)
    (h₁ : Nat.card {v : Place K F // v.deg = 1} = 6)
    (h₂ : Nat.card {v : Place K F // v.deg = 2} = m) :
    Nat.card (EffectiveDegreeTwo K F) = 21 + m := by
  classical
  let d := fun v : Place K F => v.deg
  let : Finite (WeightedEffectiveDegreeTwo.Ones d) := Nat.finite_of_card_ne_zero (by rw [h₁]; norm_num)
  let : Finite (WeightedEffectiveDegreeTwo.Twos d) := Nat.finite_of_card_ne_zero (by rw [h₂]; omega)
  letI : Fintype (WeightedEffectiveDegreeTwo.Ones d) := Fintype.ofFinite _
  have hsym : Nat.card (Sym2 (WeightedEffectiveDegreeTwo.Ones d)) = 21 := by
    rw [Nat.card_eq_fintype_card, Sym2.card, ← Nat.card_eq_fintype_card, h₁]
    decide
  change Nat.card (WeightedEffectiveDegreeTwo.EffectiveTwo d) = 21 + m
  rw [← Nat.card_congr (WeightedEffectiveDegreeTwo.enumerationEquiv d place_degree_pos),
    Nat.card_sum, hsym, h₂]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 3) ≠ 0) := ⟨by decide⟩
local instance : Fact ((104 : ZMod 5) ≠ 0) := ⟨by decide⟩

theorem actualEffectiveDegreeTwoThree_card :
    Nat.card (EffectiveDegreeTwo (ZMod 3) (actualCurveFunctionField (ZMod 3))) = 22 := by
  exact effective_degree_two_card_of_place_counts 1 (by decide)
    actualDegreeOnePlacesThree_card actualDegreeTwoPlacesThree_card

theorem actualEffectiveDegreeTwoFive_card :
    Nat.card (EffectiveDegreeTwo (ZMod 5) (actualCurveFunctionField (ZMod 5))) = 24 := by
  exact effective_degree_two_card_of_place_counts 3 (by decide)
    actualDegreeOnePlacesFive_card actualDegreeTwoPlacesFive_card

end EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts
#print axioms EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts.effective_degree_two_card_of_place_counts
#print axioms EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts.actualEffectiveDegreeTwoThree_card
#print axioms EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts.actualEffectiveDegreeTwoFive_card

end
end
theorem solution :
    Nat.card {D : AlgebraicCurve.Divisor (ZMod 3)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3)).functionField //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 22 ∧
    Nat.card {D : AlgebraicCurve.Divisor (ZMod 5)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5)).functionField //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} = 24 := by
  exact ⟨EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts.actualEffectiveDegreeTwoThree_card,
    EffectiveDegreeTwoDivisorProof.Order13EffectiveDegreeTwoDivisorCounts.actualEffectiveDegreeTwoFive_card⟩

#print axioms solution
