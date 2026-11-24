-- Prove2me | solution 1 for GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:18:26.493961+00:00
-- url     : https://prove2.me/submissions/6e2baa43-6847-4bd6-ba8d-7f6309e4a2ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictPull1InjectiveOfSepGlue
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
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
noncomputable section
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.CoefMap
namespace GlobalTheory.CatCoh.CoefMap
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1
end GlobalTheory.CatCoh.CoefMap
