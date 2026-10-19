-- Prove2me | solution 1 for MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T17:06:26.727771+00:00
-- url     : https://prove2.me/submissions/b771998e-87d1-4c4e-a22f-19a3f85dc235

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual coordinate embedding of an affine open chart
respects the structural base-field map. Named downstream consumer: diamond
function-field automorphisms over geometric extension fields of Q.
-/
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
import Definitions.Def_AlgebraicCurve_CurveModel

noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable {K : Type u} [Field K] (A : CommRingCat.{u}) [IsDomain A] [Algebra K A]
  {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
  (j : Spec A ⟶ C) [IsOpenImmersion j]

theorem solution
    (hc : j ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) (r : K) :
    coordinateEmbedding A j (algebraMap K A r) = baseToFunctionField c r := by
  letI : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  let p : Spec A := genericPoint (Spec A)
  let q := CommRingCat.ofHom (algebraMap (C.presheaf.stalk (j p)) C.functionField)
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫ j.appTop =
      CommRingCat.ofHom (algebraMap K A) ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Scheme.Hom.comp_appTop, hc]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have hj : C.presheaf.germ ⊤ (j p) trivial ≫ j.stalkMap p =
      j.appTop ≫ (Spec A).presheaf.germ ⊤ p trivial :=
    Scheme.Hom.germ_stalkMap j ⊤ p trivial
  have hq : C.presheaf.germ ⊤ (j p) trivial ≫ q = C.germToFunctionField ⊤ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Scheme.algebraMap_germ_eq_germToFunctionField C (U := ⊤) (x := j p) trivial a
  have hA : (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ p trivial =
      StructureSheaf.toStalk A p := rfl
  let k := CommRingCat.ofHom (algebraMap K A)
  let i := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  let g := (Spec A).presheaf.germ ⊤ p trivial
  let l := (asIso (j.stalkMap p)).inv
  have h2 : k ≫ StructureSheaf.toStalk A p = i ≫ c.appTop ≫ j.appTop ≫ g := by
    exact (congrArg (fun m => k ≫ m) hA.symm).trans
      ((Category.assoc k (Scheme.ΓSpecIso A).inv g).symm.trans
        ((congrArg (fun m : CommRingCat.of K ⟶ Γ(Spec A, ⊤) => m ≫ g) hΓ.symm).trans
          (Category.assoc i (c.appTop ≫ j.appTop) g)))
  have h3 : (j.appTop ≫ g) ≫ l ≫ q = C.presheaf.germ ⊤ (j p) trivial ≫ q := by
    calc
      _ = (C.presheaf.germ ⊤ (j p) trivial ≫ j.stalkMap p) ≫ l ≫ q :=
        congrArg (fun m => m ≫ l ≫ q) hj.symm
      _ = _ := by
        change (C.presheaf.germ ⊤ (j p) trivial ≫ (asIso (j.stalkMap p)).hom) ≫
          (asIso (j.stalkMap p)).inv ≫ q = _
        rw [Category.assoc, Iso.hom_inv_id_assoc]
  have H : k ≫ CommRingCat.ofHom (coordinateEmbedding A j) = i ≫ c.appTop ≫ C.germToFunctionField ⊤ := by
    calc
      _ = k ≫ StructureSheaf.toStalk A p ≫ l ≫ q :=
        congrArg (fun m => k ≫ m) (coordinate_embedding_via_stalk A j p)
      _ = (k ≫ StructureSheaf.toStalk A p) ≫ l ≫ q :=
        (Category.assoc k (StructureSheaf.toStalk A p) (l ≫ q)).symm
      _ = (i ≫ c.appTop ≫ j.appTop ≫ g) ≫ l ≫ q :=
        congrArg (fun m => m ≫ l ≫ q) h2
      _ = i ≫ c.appTop ≫ ((j.appTop ≫ g) ≫ l ≫ q) := by simp only [Category.assoc]
      _ = i ≫ c.appTop ≫ C.presheaf.germ ⊤ (j p) trivial ≫ q :=
        congrArg (fun m => i ≫ c.appTop ≫ m) h3
      _ = _ := congrArg (fun m => i ≫ c.appTop ≫ m) hq
  exact congrArg (fun g : CommRingCat.of K ⟶ C.functionField => g r) H

#print axioms solution
