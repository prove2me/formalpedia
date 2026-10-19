-- Prove2me | solution 1 for MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:23:08.048238+00:00
-- url     : https://prove2.me/submissions/02b03812-311e-43a0-8ecb-8d1aa70376d8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compatibility of the constructed coordinate embeddings with
an affine open restriction. Named downstream consumer: comparison of the
ordinary and reciprocal Pell functions on the order-13 curve.
-/
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
noncomputable section
universe u
open MazurTransfer
open MazurTransfer.AffineOpenChartFunctionFieldNaturality
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldStalk

variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

variable (B : CommRingCat.{u}) [IsDomain B] (φ : A ⟶ B)
    [IsOpenImmersion (Spec.map φ)]

theorem solution :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      φ ≫ CommRingCat.ofHom (coordinateEmbedding B (Spec.map φ ≫ j)) := by
  let p : Spec B := genericPoint (Spec B)
  let h := Spec.map φ
  have Hspec : StructureSheaf.toStalk A (h p) ≫ h.stalkMap p =
      φ ≫ StructureSheaf.toStalk B p := stalkMap_toStalk φ p
  let c := CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j (h p))) X.functionField)
  let lA := (asIso (j.stalkMap (h p))).inv
  let lB := (asIso (h.stalkMap p)).inv
  let lC := (asIso ((h ≫ j).stalkMap p)).inv
  have Hinv : lC = lB ≫ lA := by
    have Hright : 𝟙 _ = ((h ≫ j).stalkMap p) ≫ (lB ≫ lA) := by
      calc
        _ = (j.stalkMap (h p) ≫ h.stalkMap p) ≫ (lB ≫ lA) := by
          dsimp [lA, lB]
          simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]
        _ = _ := congrArg (fun k => k ≫ (lB ≫ lA))
          (Scheme.Hom.stalkMap_comp h j p).symm
    exact (Category.comp_id lC).symm.trans
      ((asIso ((h ≫ j).stalkMap p)).inv_comp_eq.mpr Hright)
  have Hcancel : (StructureSheaf.toStalk A (h p) ≫ h.stalkMap p) ≫ lB =
      StructureSheaf.toStalk A (h p) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => StructureSheaf.toStalk A (h p) ≫ k)
        (IsIso.hom_inv_id (h.stalkMap p))).trans (Category.comp_id _))
  calc
    _ = StructureSheaf.toStalk A (h p) ≫ lA ≫ c :=
      coordinate_embedding_via_stalk A j (h p)
    _ = ((StructureSheaf.toStalk A (h p) ≫ h.stalkMap p) ≫ lB) ≫ lA ≫ c :=
      congrArg (fun k => k ≫ lA ≫ c) Hcancel.symm
    _ = (φ ≫ StructureSheaf.toStalk B p) ≫ lB ≫ lA ≫ c :=
      congrArg (fun k => (k ≫ lB) ≫ lA ≫ c) Hspec
    _ = φ ≫ StructureSheaf.toStalk B p ≫ (lB ≫ lA) ≫ c :=
      congrArg (fun k => φ ≫ StructureSheaf.toStalk B p ≫ k)
        (Category.assoc lB lA c).symm
    _ = φ ≫ StructureSheaf.toStalk B p ≫ lC ≫ c :=
      congrArg (fun k => φ ≫ StructureSheaf.toStalk B p ≫ k ≫ c) Hinv.symm
    _ = _ := congrArg (fun k => φ ≫ k)
      (coordinate_embedding_via_stalk B (h ≫ j) p).symm


#print axioms solution
