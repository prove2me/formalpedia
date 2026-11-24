-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.glue_comma_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:18:24.017388+00:00
-- url     : https://prove2.me/submissions/a7f0deb9-50db-44b6-bbad-22c719b2d4b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_std
import Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std


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
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T s hs
  have key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂) := by
    intro t₁ t₂ u₁ u₂ S w₁ w₂
    obtain ⟨n, b, hb, hb'⟩ := hdir t₁ t₂ S w₁ w₂
    refine sub_eq_zero.1 (sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)
    obtain ⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩ := hb' i S' u' hi
    have e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]
    have e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]
    have e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov T
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t, v, w, -⟩ := hb' i S u hi
      exact ⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t, v, w, e⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩
    rw [← e, ← e', ← mp_comp]
    exact key _ _ _ _ _ _ _
  refine ⟨x, fun t u ↦ ?_⟩
  have hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine sub_eq_zero.1 (sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]
end GlobalTheory.CatCoh.Desc
