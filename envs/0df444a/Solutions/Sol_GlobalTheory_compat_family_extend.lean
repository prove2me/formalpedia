-- Prove2me | solution 1 for GlobalTheory.compat_family_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:06.780996+00:00
-- url     : https://prove2.me/submissions/dc5d330a-14dc-4ea9-9a8c-f057d0bcd829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatFamilyExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) → ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t := by
  intro R _ C _ C' _ F G hsep hglue g' hg'
  choose g hg using fun T : C ↦ hglue T (fun t _ ↦ g' t) fun t t' _ a ↦ hg' a
  refine ⟨g, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · refine sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)
    rw [map_sub, ← mp_comp, hg, hg, sub_self]
  · have h := hg (G.obj t) t (𝟙 _)
    rwa [mp_id] at h
end GlobalTheory
