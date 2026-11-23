-- Prove2me | solution 1 for GlobalTheory.GlueModels.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:02.971098+00:00
-- url     : https://prove2.me/submissions/9c0b19e7-5531-4af1-9754-752d07f404bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GlueModels
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GlueModels
theorem _root_.solution {X U V W Y : Scheme.{0}} {u : U ⟶ X} {v : V ⟶ X} {p : W ⟶ U} {q : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v] (h : IsPullback p q u v)
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (a : U ⟶ Y) (b : V ⟶ Y) (hab : p ≫ a = q ≫ b) :
    ∃ φ : X ⟶ Y, u ≫ φ = a ∧ v ≫ φ = b := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  let m : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) a b i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  suffices hm : _ from ⟨𝒰.glueMorphisms m hm, 𝒰.ι_glueMorphisms m hm false, 𝒰.ι_glueMorphisms m hm true⟩
  · rintro (_ | _) (_ | _)
    · change pullback.fst u u ≫ a = pullback.snd u u ≫ a
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst u v ≫ a = pullback.snd u v ≫ b
      rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v u ≫ b = pullback.snd v u ≫ a
      rw [← h.flip.isoPullback_inv_fst, ← h.flip.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v v ≫ b = pullback.snd v v ≫ b
      rw [fst_eq_snd_of_mono_eq]
end GlobalTheory.GlueModels
