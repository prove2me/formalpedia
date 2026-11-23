-- Prove2me | solution 1 for GlobalTheory.UU.TorusCompat.isMonHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:57.257665+00:00
-- url     : https://prove2.me/submissions/55f1ba4f-0216-4aaf-b5b3-41a736d720f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_GlobalTheory_SplitTorus_mul_left_bcMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
section API
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G'' : Over S''} {G' : Over S'} {G : Over S}
private theorem torusCompat_mul_comp [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsGrpPullback G' G f F) {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G} [IsMonHom i]
    (h : TorusCompat f F i' i) {T : Over S'} (u v : T ⟶ splitTorus S' X) :
    (u * v) ≫ i' = (u ≫ i') * (v ≫ i') := by
  rw [torusCompat_iff] at h
  let p : Over.mk (T.hom ≫ f) ⟶ splitTorus S X :=
    Over.homMk (u.left ≫ bcMap f X) (by simp [bcMap_hom])
  let q : Over.mk (T.hom ≫ f) ⟶ splitTorus S X :=
    Over.homMk (v.left ≫ bcMap f X) (by simp [bcMap_hom])
  have hpq : (p * q).left = (u * v).left ≫ bcMap f X :=
    SplitTorus.mul_left_bcMap f X T u v p q rfl rfl
  have key : ((p ≫ i) * (q ≫ i)).left = ((u ≫ i') * (v ≫ i')).left ≫ F :=
    hF.2 T (u ≫ i') (v ≫ i') (p ≫ i) (q ≫ i)
      (by show (u.left ≫ bcMap f X) ≫ i.left = (u.left ≫ i'.left) ≫ F; rw [Category.assoc, h, Category.assoc])
      (by show (v.left ≫ bcMap f X) ≫ i.left = (v.left ≫ i'.left) ≫ F; rw [Category.assoc, h, Category.assoc])
  apply Over.OverMorphism.ext
  apply hF.1.hom_ext
  · calc ((u * v) ≫ i').left ≫ F = (u * v).left ≫ (i'.left ≫ F) := by simp
      _ = (u * v).left ≫ (bcMap f X ≫ i.left) := by rw [h]
      _ = (p * q).left ≫ i.left := by rw [hpq, Category.assoc]
      _ = ((p ≫ i) * (q ≫ i)).left := by rw [← MonObj.mul_comp]; rfl
      _ = _ := key
  · simp
end API
example : TorusCompat (red (Ideal.span {(2 : ZMod 4)}))
    (SplitTorus.bcMap (red (Ideal.span {(2 : ZMod 4)})) ℤ) (𝟙 (splitTorus _ ℤ)) (𝟙 (splitTorus _ ℤ)) :=
  torusCompat_bcMap _
example (S : Scheme.{0}) (G : Over S) (i : splitTorus S ℤ ⟶ G) : TorusCompat (𝟙 S) (𝟙 _) i i :=
  TorusCompat.refl i
example : ¬ TorusCompat (𝟙 (Spec (CommRingCat.of ℚ))) (𝟙 _)
    (1 : splitTorus _ ℤ ⟶ splitTorus _ ℤ) (𝟙 (splitTorus _ ℤ)) := by
  rw [torusCompat_id_iff]
  intro h
  let S := Spec (CommRingCat.of ℚ)
  have hall : ∀ t : Over.mk (𝟙 S) ⟶ splitTorus S ℤ, t = 1 := fun t => by
    rw [← Category.comp_id t, ← h, MonObj.comp_one]
  let u : Γ(S, ⊤)ˣ := -1
  have h1 := SplitTorus.val_ofVal (T := Over.mk (𝟙 S)) (zmultiplesHom _ (Additive.ofMul u)) 1
  rw [hall (SplitTorus.ofVal _), SplitTorus.val_one] at h1
  have h2 : u = 1 := Units.ext (by simpa using h1.symm)
  have h3 := congrArg (fun v : Γ(S, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom v.val) h2
  simp only [u, Units.val_neg, Units.val_one, map_neg, map_one] at h3
  norm_num at h3
end GlobalTheory.UU
end
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G'' : Over S''} {G' : Over S'} {G : Over S}
namespace GlobalTheory.UU
namespace TorusCompat
theorem _root_.solution [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsGrpPullback G' G f F) {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G} [IsMonHom i]
    (h : TorusCompat f F i' i) : IsMonHom i' := by
  have hm : ∀ {T : Over S'} (u v : T ⟶ splitTorus S' X), (u * v) ≫ i' = (u ≫ i') * (v ≫ i') :=
    fun u v => torusCompat_mul_comp hF h u v
  have one_eq : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := fun M _ => by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  constructor
  · have he := hm (1 : 𝟙_ (Over S') ⟶ splitTorus S' X) 1
    rw [_root_.mul_one] at he
    have h1 : (1 : 𝟙_ (Over S') ⟶ splitTorus S' X) ≫ i' = 1 := by simpa using he.symm
    rw [one_eq, one_eq] at h1
    exact h1
  · have hμ := hm (fst (splitTorus S' X) (splitTorus S' X)) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] at hμ
    exact hμ
end TorusCompat
end GlobalTheory.UU
