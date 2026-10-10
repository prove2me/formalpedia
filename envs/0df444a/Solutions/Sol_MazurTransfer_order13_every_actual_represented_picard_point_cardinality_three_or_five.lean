-- Prove2me | solution 1 for MazurTransfer.order13_every_actual_represented_picard_point_cardinality_three_or_five
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T01:10:55.414294+00:00
-- url     : https://prove2.me/submissions/dc07ec59-1ff8-4d16-8d27-be677e2c3c20

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Genuine relative Picard universality reuses official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: actual point count 19 and finiteness for every representation
of the normalized degree-zero Picard functor over F3 and F5.
Named downstream consumer: the actual Picard models chosen for compatible
Jacobian good reduction. No point count, point dictionary or rank is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_represented_picard_point_cardinality_three_or_five

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The actual relative Picard universality interface reuses official Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: two genuine representations of the same relative Picard
condition have equivalent field-valued and arbitrary scheme-valued point
sets, using their universal Poincare families rather than an assumed dictionary.
Named downstream consumer: transporting the actual order-13 finite-field
point counts to a representing model chosen for compatible good reduction.
-/

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

namespace MazurTransfer.RepresentedPicardPointComparison

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable {c : C ⟶ Spec (CommRingCat.of R)}
variable {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
variable {P : SubPicCondition c ε} {D D' : RelativePic0Designation R c}

noncomputable def pointEquiv
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c ε P D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t D.toBase ≃ SchemeHomOver t D'.toBase := by
  let f : SchemeHomOver t D.toBase → SchemeHomOver t D'.toBase := fun a =>
    h'.classify t (h.poincare.pullbackAlong a)
      (P.pullback_mem D.toBase t a h.poincare h.poincare_mem)
  let g : SchemeHomOver t D'.toBase → SchemeHomOver t D.toBase := fun a =>
    h.classify t (h'.poincare.pullbackAlong a)
      (P.pullback_mem D'.toBase t a h'.poincare h'.poincare_mem)
  refine ⟨f, g, ?_, ?_⟩
  · intro a
    apply h.ext_of_iso
    obtain ⟨i⟩ := h.classify_spec t (h'.poincare.pullbackAlong (f a))
      (P.pullback_mem D'.toBase t (f a) h'.poincare h'.poincare_mem)
    obtain ⟨j⟩ := h'.classify_spec t (h.poincare.pullbackAlong a)
      (P.pullback_mem D.toBase t a h.poincare h.poincare_mem)
    exact ⟨i ≪≫ j⟩
  · intro a
    apply h'.ext_of_iso
    obtain ⟨i⟩ := h'.classify_spec t (h.poincare.pullbackAlong (g a))
      (P.pullback_mem D.toBase t (g a) h.poincare h.poincare_mem)
    obtain ⟨j⟩ := h.classify_spec t (h'.poincare.pullbackAlong a)
      (P.pullback_mem D'.toBase t a h'.poincare h'.poincare_mem)
    exact ⟨i ≪≫ j⟩

def overHomEquivSchemeHom {S T Y : Scheme.{u}} (t : T ⟶ S) (y : Y ⟶ S) :
    (Over.mk t ⟶ Over.mk y) ≃ SchemeHomOver t y :=
  { toFun := fun f => ⟨f.left, by simpa only [Over.mk_left, Over.mk_hom] using Over.w f⟩
    invFun := fun f => Over.homMk f.1 f.2
    left_inv := by intro f; apply Over.OverMorphism.ext; rfl
    right_inv := by intro f; apply Subtype.ext; rfl }

end MazurTransfer.RepresentedPicardPointComparison

#print axioms MazurTransfer.RepresentedPicardPointComparison.pointEquiv
#print axioms MazurTransfer.RepresentedPicardPointComparison.overHomEquivSchemeHom

end

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem solution
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    ∀ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
      (D : RelativePic0Designation (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
      (h : RepresentsRelSubPic
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε
        (algEquivZeroCut
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε) D),
      Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) ∧
      Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) = 19 ∧
      Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) ∧
      Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) = 19 := by
  letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
  intro ε D h
  obtain ⟨D₀, h₀, _, _, hfinite₀, hcard₀⟩ :=
    MazurTransfer.order13_actual_represented_picard_point_cardinality_three_or_five q hq ε
  let e := MazurTransfer.RepresentedPicardPointComparison.pointEquiv h₀ h
    (𝟙 (Spec (CommRingCat.of (ZMod q))))
  letI := hfinite₀
  have hfinite : Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) :=
    Finite.of_surjective e e.surjective
  have hcard : Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) = 19 :=
    (Nat.card_congr e).symm.trans hcard₀
  let eOver := MazurTransfer.RepresentedPicardPointComparison.overHomEquivSchemeHom
    (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase
  letI := hfinite
  exact ⟨hfinite, hcard, Finite.of_injective eOver eOver.injective,
    (Nat.card_congr eOver).trans hcard⟩

#print axioms solution
