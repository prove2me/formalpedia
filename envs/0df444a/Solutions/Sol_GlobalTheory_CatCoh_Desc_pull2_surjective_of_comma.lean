-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:31.116461+00:00
-- url     : https://prove2.me/submissions/5d0bd47b-e5a4-44aa-b451-ac43a1a20e65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentRestrictionEquiv
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G sep glue van1 van2 c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ t t' t'' : C', (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t''),
      ∀ t t' t'' a b, Y t t' t'' a b = y.1 t t' t'' a b := ⟨y.1, fun _ _ _ _ _ ↦ rfl⟩
  have hy : ∀ t t' t'' t''' (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
      mp F (G.map c) (Y t t' t'' a b) + Y t t'' t''' (a ≫ b) c =
        Y t t' t''' a (b ≫ c) + Y t' t'' t''' b c := by
    intro t t' t'' t''' a b c
    simp only [hY]
    exact y.2 a b c
  choose h hh using fun T : C ↦ van2 T (fun t t' t'' _ a b ↦ Y t t' t'' a b)
    (fun t t' t'' t''' _ a b c ↦ hy t t' t'' t''' a b c)
  choose m hm using fun (T T' : C) (φ : T ⟶ T') ↦
    van1 T' (fun t t' u a ↦ h T t t' (φ ≫ u) a - h T' t t' u a) (fun t t' t'' u a b ↦ by
      have k1 := hh T t t' t'' (φ ≫ u) a b
      have k2 := hh T' t t' t'' u a b
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k2 - k1)
  choose x hx using fun (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦
    glue T'' (fun t u ↦ m T T' φ t (ψ ≫ u) + m T' T'' ψ t u - m T T'' (φ ≫ ψ) t u)
      (fun t t' u a ↦ by
        have k1 := hm T T' φ t t' (ψ ≫ u) a
        have k2 := hm T' T'' ψ t t' u a
        have k3 := hm T T'' (φ ≫ ψ) t t' u a
        simp only [map_sub, map_add, Category.assoc] at k1 k3 ⊢
        linear_combination k1 + k2 - k3)
  refine ⟨H2.mk F ⟨fun T T' T'' φ ψ ↦ x T T' T'' φ ψ,
    fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun t u ↦ ?_)⟩, ?_⟩
  · have k1 := hx _ _ _ φ ψ t (χ ≫ u)
    have k2 := hx _ _ _ (φ ≫ ψ) χ t u
    have k3 := hx _ _ _ φ (ψ ≫ χ) t u
    have k4 := hx _ _ _ ψ χ t u
    simp only [map_sub, map_add, Category.assoc, mp_comp] at k1 k2 k3 k4 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a, ?_⟩
    funext t t' t'' a b
    simp only [Pi.sub_apply]
    rw [← hY]
    have k1 := hx _ _ _ (G.map a) (G.map b) t'' (𝟙 _)
    have k2 := hm _ _ (G.map a) t' t'' (𝟙 _) b
    have k3 := hh _ t t' t'' (𝟙 _) a b
    simp only [mp_id, Category.id_comp, Category.comp_id] at k1 k2 k3
    change mp F (G.map b) (m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a) -
        (m _ _ (G.map (a ≫ b)) t'' (𝟙 _) - h _ t t'' (𝟙 _) (a ≫ b)) +
        (m _ _ (G.map b) t'' (𝟙 _) - h _ t' t'' (𝟙 _) b) =
      x _ _ _ (G.map a) (G.map b) - Y t t' t'' a b
    rw [G.map_comp]
    simp only [map_sub]
    linear_combination -k1 - k2 - k3
end GlobalTheory.CatCoh.Desc
