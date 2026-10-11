-- Prove2me | solution 1 for MazurTransfer.affine_chart_coordinate_embedding_base_scalars
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T17:10:52.355978+00:00
-- url     : https://prove2.me/submissions/c1b1a5be-70f9-4322-8a55-65ae09a1e04b

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an integral affine open chart supplies its actual coordinate
algebra as a fraction-ring base for the scheme's existing function field.
Named downstream consumer: the two order-13 chart embeddings and the Pell
principal divisor. This constructs the maps from the open immersion's stalk
isomorphism at the generic point, without a supplied field equivalence.
-/

noncomputable section
universe u
namespace AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionField
open AlgebraicGeometry CategoryTheory
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

def functionFieldIso : X.functionField ≅ (Spec A).functionField :=
  eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint (Spec A)))

def coordinateEmbedding : A →+* X.functionField :=
  (functionFieldIso A j).inv.hom.comp (algebraMap A (Spec A).functionField)

def coordinateAlgebra : Algebra A X.functionField := (coordinateEmbedding A j).toAlgebra

theorem coordinateEmbedding_injective : Function.Injective (coordinateEmbedding A j) :=
  (ConcreteCategory.bijective_of_isIso (functionFieldIso A j).inv).1.comp
    (IsFractionRing.injective A (Spec A).functionField)

theorem coordinate_isFractionRing :
    letI := coordinateAlgebra A j
    IsFractionRing A X.functionField := by
  letI := coordinateAlgebra A j
  apply IsFractionRing.of_algEquiv (R := A) (K := (Spec A).functionField)
  refine AlgEquiv.ofRingEquiv (f := (functionFieldIso A j).symm.commRingCatIsoToRingEquiv) ?_
  intro a
  rfl

end AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionField
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionField.coordinateEmbedding_injective
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionField.coordinate_isFractionRing

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the chart's generic field isomorphism commutes with the
actual maps from every stalk. Named downstream consumer: identifying the
two Pell valuation rings with the two literal infinity section centers.
-/

noncomputable section
universe u
namespace AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldStalk
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField
private theorem specializes_cast (Y : Scheme.{u}) {x y x' : Y}
    (h : x ⤳ y) (h' : x' ⤳ y) (e : x = x') :
    Y.presheaf.stalkSpecializes h' ≫ eqToHom (congrArg Y.presheaf.stalk e.symm) =
      Y.presheaf.stalkSpecializes h := by
  subst x'
  simp

variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

def chartPrime (p : Spec A) : PrimeSpectrum A := p

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

def localStalkIso (p : Spec A) :
    CommRingCat.of (Localization.AtPrime (chartPrime A p).asIdeal) ≅ X.presheaf.stalk (j p) :=
  (Spec.stalkIso A (chartPrime A p)).symm ≪≫ (asIso (j.stalkMap p)).symm

theorem local_stalk_coordinate_commutes (p : Spec A) :
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

end AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldStalk
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldStalk.stalk_map_commutes
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compatibility of the constructed coordinate embeddings with
an affine open restriction. Named downstream consumer: comparison of the
ordinary and reciprocal Pell functions on the order-13 curve.
-/

noncomputable section
universe u
namespace AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldNaturality
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldStalk

variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

theorem coordinate_embedding_via_stalk (p : Spec A) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      StructureSheaf.toStalk A p ≫ (asIso (j.stalkMap p)).inv ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField) := by
  let c := CommRingCat.ofHom (algebraMap (X.presheaf.stalk (j p)) X.functionField)
  let e := (functionFieldIso A j).hom
  let q := CommRingCat.ofHom (algebraMap ((Spec A).presheaf.stalk p) (Spec A).functionField)
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
    _ = _ := by
      let l := (asIso (j.stalkMap p)).inv
      have Hdiag : (l ≫ c) ≫ e = q :=
        (Category.assoc l c e).trans
          ((congrArg (fun k => l ≫ k) (stalk_map_commutes A j p)).trans
            ((Category.assoc l (j.stalkMap p) q).symm.trans
              ((congrArg (fun k => k ≫ q) (IsIso.inv_hom_id (j.stalkMap p))).trans
                (Category.id_comp q))))
      exact (congrArg (fun k => StructureSheaf.toStalk A p ≫ k) Hdiag.symm).trans
        (Category.assoc (StructureSheaf.toStalk A p) (l ≫ c) e).symm

variable (B : CommRingCat.{u}) [IsDomain B] (φ : A ⟶ B)
    [IsOpenImmersion (Spec.map φ)]

theorem coordinate_embedding_restriction :
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

theorem coordinate_embedding_restriction_of_eq
    (k : Spec B ⟶ X) [IsOpenImmersion k] (hk : Spec.map φ ≫ j = k) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      φ ≫ CommRingCat.ofHom (coordinateEmbedding B k) := by
  subst k
  exact coordinate_embedding_restriction A j B φ

end AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldNaturality
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_via_stalk
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_restriction
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldNaturality.coordinate_embedding_restriction_of_eq

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual coordinate embedding of an affine open chart
respects the structural base-field map. Named downstream consumer: diamond
function-field automorphisms over geometric extension fields of Q.
-/

noncomputable section
universe u
namespace AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable {K : Type u} [Field K] (A : CommRingCat.{u}) [IsDomain A] [Algebra K A]
  {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
  (j : Spec A ⟶ C) [IsOpenImmersion j]

theorem coordinateEmbedding_algebraMap
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

end AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility
#print axioms AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap

end

open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
theorem solution
    {K : Type u} [Field K] (A : CommRingCat.{u}) [IsDomain A] [Algebra K A]
    {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
    (j : Spec A ⟶ C) [IsOpenImmersion j]
    (hc : j ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) (r : K) :
    let e : C.functionField ≅ (Spec A).functionField :=
      eqToIso (congrArg C.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
        asIso (j.stalkMap (genericPoint (Spec A)))
    e.inv.hom (algebraMap A (Spec A).functionField (algebraMap K A r)) = baseToFunctionField c r := by
  exact AffineChartScalarCompatibilityPublicProof.MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap A c j hc r
#print axioms solution
