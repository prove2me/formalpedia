-- Prove2me | solution 1 for MazurTransfer.AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T12:37:22.453088+00:00
-- url     : https://prove2.me/submissions/e7634066-101f-4ec3-a005-a8d7910e3a0d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the chart's generic field isomorphism commutes with the
actual maps from every stalk. Named downstream consumer: identifying the
two Pell valuation rings with the two literal infinity section centers.
-/
import Definitions.Def_MazurTransfer_AffineChartLocalStalkData
noncomputable section
universe u
open MazurTransfer AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldStalk
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

namespace MazurTransfer.AffineChartStalkCompatibilityHelpers20261017
private theorem specializes_cast (Y : Scheme.{u}) {x y x' : Y}
    (h : x ⤳ y) (h' : x' ⤳ y) (e : x = x') :
    Y.presheaf.stalkSpecializes h' ≫ eqToHom (congrArg Y.presheaf.stalk e.symm) =
      Y.presheaf.stalkSpecializes h := by
  subst x'
  simp

theorem stalk_map_commutes (p : Spec A) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField) ≫
      (functionFieldIso A j).hom =
        j.stalkMap p ≫ CommRingCat.ofHom
          (algebraMap ((Spec A).presheaf.stalk p) (Spec A).functionField) := by
  have h := genericPoint_eq_of_isOpenImmersion j
  change X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫
    (eqToHom (congrArg X.presheaf.stalk h.symm) ≫ j.stalkMap (genericPoint (Spec A))) =
      j.stalkMap p ≫ (Spec A).presheaf.stalkSpecializes
        ((genericPoint_spec (Spec A)).specializes trivial)
  have H := j.stalkSpecializes_stalkMap (genericPoint (Spec A)) p
    ((genericPoint_spec (Spec A)).specializes trivial)
  rw [← Category.assoc, specializes_cast X
    (j.base.hom.map_specializes ((genericPoint_spec (Spec A)).specializes trivial))
    ((genericPoint_spec X).specializes trivial) h]
  exact H

end MazurTransfer.AffineChartStalkCompatibilityHelpers20261017
open MazurTransfer.AffineChartStalkCompatibilityHelpers20261017
theorem solution (p : Spec A) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      CommRingCat.ofHom (algebraMap A (Localization.AtPrime (chartPrime A p).asIdeal)) ≫
        (localStalkIso A j p).hom ≫
          CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField) := by
  let s : CommRingCat.of (Localization.AtPrime (chartPrime A p).asIdeal) ⟶
      (Spec A).presheaf.stalk p := (Spec.stalkIso A (chartPrime A p)).inv
  let l := (localStalkIso A j p).hom
  let c := CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField)
  let e := (functionFieldIso A j).hom
  let q := CommRingCat.ofHom (algebraMap ((Spec A).presheaf.stalk p) (Spec A).functionField)
  have Hiso : l ≫ j.stalkMap p = s := by
    exact (Category.assoc s (inv (j.stalkMap p)) (j.stalkMap p)).trans
      ((congrArg (fun k => s ≫ k) (IsIso.inv_hom_id (j.stalkMap p))).trans
        (Category.comp_id s))
  have Hdiag : (l ≫ c) ≫ e = s ≫ q := by
    exact (Category.assoc l c e).trans
      ((congrArg (fun k => l ≫ k) (stalk_map_commutes A j p)).trans
        ((Category.assoc l (j.stalkMap p) q).symm.trans
          (congrArg (fun k => k ≫ q) Hiso)))
  have H : CommRingCat.ofHom (algebraMap A (Localization.AtPrime (chartPrime A p).asIdeal)) ≫
      s = StructureSheaf.toStalk A p := by
    ext a
    let : Algebra A ((structurePresheafInCommRingCat A).stalk (chartPrime A p)) :=
      (StructureSheaf.toStalk A (chartPrime A p)).hom.toAlgebra
    exact (StructureSheaf.stalkIso A (chartPrime A p)).commutes a
  apply (cancel_mono (functionFieldIso A j).hom).mp
  have Hcoordinate : CommRingCat.ofHom (coordinateEmbedding A j) ≫ e =
      CommRingCat.ofHom (algebraMap A (Spec A).functionField) := by
    exact (Category.assoc _ (functionFieldIso A j).inv e).trans
      ((congrArg (fun k => CommRingCat.ofHom (algebraMap A (Spec A).functionField) ≫ k)
        (Iso.inv_hom_id (functionFieldIso A j))).trans (Category.comp_id _))
  calc
    _ = CommRingCat.ofHom (algebraMap A (Spec A).functionField) := Hcoordinate
    _ = StructureSheaf.toStalk A p ≫ q :=
      (StructureSheaf.toStalk_stalkSpecializes
        ((genericPoint_spec (Spec A)).specializes trivial)).symm
    _ = (CommRingCat.ofHom (algebraMap A (Localization.AtPrime (chartPrime A p).asIdeal)) ≫ s) ≫ q :=
      congrArg (fun k => k ≫ q) H.symm
    _ = _ := by
      have hh := congrArg (fun k =>
        CommRingCat.ofHom (algebraMap A (Localization.AtPrime (chartPrime A p).asIdeal)) ≫ k) Hdiag.symm
      exact (Category.assoc _ s q).trans (hh.trans (Category.assoc _ (l ≫ c) e).symm)

#print axioms solution
