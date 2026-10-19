-- Prove2me | solution 1 for MazurTransfer.AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T18:16:27.243282+00:00
-- url     : https://prove2.me/submissions/cbbc4d27-b9e0-4191-b6e0-008ef64bbf94

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit coordinate embedding of an integral affine
open chart recovers the scheme's literal generic-stalk morphism.
Named downstream consumer: compatibility of the order-13 generic embedding
with extension of the base field.
-/
import Definitions.Def_MazurTransfer_AffineOpenChartFunctionField

noncomputable section
universe u
open MazurTransfer
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField
variable (A : CommRingCat.{u}) [IsDomain A] {C : Scheme.{u}} [IsIntegral C]
    (j : Spec A ⟶ C) [IsOpenImmersion j]

private theorem fromSpecStalk_cast {x y : C} (e : x = y) :
    Spec.map (eqToHom (congrArg C.presheaf.stalk e)) ≫ C.fromSpecStalk x =
      C.fromSpecStalk y := by
  subst y
  simp

theorem solution :
    Spec.map (CommRingCat.ofHom (coordinateEmbedding A j)) ≫ j =
      C.fromSpecStalk (genericPoint C) := by
  let p : Spec A := genericPoint (Spec A)
  have hp : j p = genericPoint C := genericPoint_eq_of_isOpenImmersion j
  have hη : Spec.map (CommRingCat.ofHom (algebraMap A (Spec A).functionField)) =
      (Spec A).fromSpecStalk p := by
    exact (Spec.fromSpecStalk_eq' A p).symm
  change Spec.map (CommRingCat.ofHom (algebraMap A (Spec A).functionField) ≫
    (functionFieldIso A j).inv) ≫ j = _
  rw [Spec.map_comp, Category.assoc, hη]
  have hj := Scheme.SpecMap_stalkMap_fromSpecStalk j (x := p)
  have hi : (functionFieldIso A j).inv =
      (asIso (j.stalkMap p)).inv ≫ eqToHom (congrArg C.presheaf.stalk hp) := by
    simp [functionFieldIso, p]
  rw [hi, Spec.map_comp, Category.assoc, ← hj]
  have hcancel : j.stalkMap p ≫ (asIso (j.stalkMap p)).inv = 𝟙 _ :=
    (asIso (j.stalkMap p)).hom_inv_id
  rw [← Spec.map_comp_assoc (j.stalkMap p) (asIso (j.stalkMap p)).inv,
    hcancel, Spec.map_id, Category.id_comp]
  exact fromSpecStalk_cast hp

#print axioms solution
