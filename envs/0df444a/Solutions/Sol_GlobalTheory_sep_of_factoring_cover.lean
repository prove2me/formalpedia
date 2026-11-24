-- Prove2me | solution 1 for GlobalTheory.sep_of_factoring_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:19:52.421331+00:00
-- url     : https://prove2.me/submissions/89a777c4-fd86-48a9-a038-d4d65b164da9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepOfFactoringCover
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) := by
  intro R _ C _ C' _ F G H hcov T x hx
  obtain ⟨n, b, hb, h⟩ := hcov T
  refine Desc.sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t, v, w, rfl⟩ := h i S u hi
  rw [mp_comp, hx t v, map_zero]
end GlobalTheory
