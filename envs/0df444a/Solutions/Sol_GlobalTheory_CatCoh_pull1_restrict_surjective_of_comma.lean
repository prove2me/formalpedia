-- Prove2me | solution 1 for GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:14:29.540063+00:00
-- url     : https://prove2.me/submissions/f38ce188-4f50-4410-8d45-a114e2dda3a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_Pull1RestrictSurjectiveOfComma
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
open GlobalTheory GlobalTheory.CatCoh
namespace GlobalTheory.CatCoh
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) → Function.Surjective (CoefMap.restrict F G).pull1 := by
  intro R _ C _ C' _ F G hsep hglue hvan c
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
  have hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a := fun T ↦
    hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'
  choose b hb using hb
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := hb T t t' (φ ≫ u) a
    have k2 := hb T' t t' u a
    rw [Category.assoc] at k1
    rw [map_sub]
    linear_combination k1 - k2
  choose x hx using hx
  have hxc : x ∈ Z1 F := fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by
    have k1 := hx T T'' (φ ≫ ψ) t u
    have k2 := hx T T' φ t (ψ ≫ u)
    have k3 := hx T' T'' ψ t u
    rw [mp_comp] at k2
    simp only [map_sub, map_add, Category.assoc] at k1 k2 ⊢
    linear_combination k1 - k2 - k3)
  refine ⟨H1.mk F ⟨x, hxc⟩, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩
  funext t t' a
  have k1 := hx _ _ (G.map a) t' (𝟙 _)
  have k2 := hb (G.obj t) t t' (𝟙 _) a
  rw [mp_id, Category.comp_id] at k1
  rw [Category.id_comp] at k2
  show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)
  rw [map_neg]
  linear_combination -k1 - k2
end GlobalTheory.CatCoh
