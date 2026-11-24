-- Prove2me | solution 1 for GlobalTheory.CatCoh.pull2_restrict_injective_of_comma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:32.212858+00:00
-- url     : https://prove2.me/submissions/3880944d-e163-4765-809c-4b7e3eb1464b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentInjective
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
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
open GlobalTheory GlobalTheory.CatCoh
namespace GlobalTheory.CatCoh
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G hsep hglue hvan
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨y0, hy0⟩ := hc
  obtain ⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t')
      (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b
        = z.1 _ _ _ (G.map a) (G.map b) := ⟨y0, fun t t' t'' a b ↦
    congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩
  have hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u)
        = z.1 _ _ _ u (G.map a) - y t t' a := fun T ↦
    hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by
      have k1 := z.2 u (G.map a) (G.map b)
      have k2 := hy' t t' t'' a b
      rw [Functor.map_comp]
      simp only [map_sub]
      linear_combination k2 - k1
  choose g hg using hg
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t),
      mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := z.2 φ u (G.map a)
    have k2 := hg T t t' (φ ≫ u) a
    have k3 := hg T' t t' u a
    rw [Category.assoc] at k2
    simp only [map_sub, map_add]
    linear_combination -k1 - k2 + k3
  choose x hx using hx
  refine H2.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' T'' φ ψ
  refine sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)
  have k1 := z.2 φ ψ u
  have k2 := hx T T' φ t (ψ ≫ u)
  have k3 := hx T T'' (φ ≫ ψ) t u
  have k4 := hx T' T'' ψ t u
  rw [mp_comp] at k2
  rw [d1_apply]
  simp only [map_sub, map_add, Category.assoc] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1
end GlobalTheory.CatCoh
