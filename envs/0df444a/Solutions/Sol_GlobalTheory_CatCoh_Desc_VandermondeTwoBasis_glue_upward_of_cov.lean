-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:43.502162+00:00
-- url     : https://prove2.me/submissions/a372eae0-8ff4-40fb-a853-71347a27a327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGluedSectionUpwardFamilyStandardCover
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_span_map_eq_top
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_std
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t Sg hup hcov s hs
  have key : ∀ (t₁ t₂ : C') (a₁ : t ⟶ t₁) (a₂ : t ⟶ t₂), Sg t₁ a₁ → Sg t₂ a₂ → ∀ (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ a₁) = mp F w₂ (s t₂ a₂) := by
    intro t₁ t₂ a₁ a₂ h₁ h₂ S w₁ w₂
    refine sub_eq_zero.1 (Basis.eq_zero_of_local F G H hdir ⟨w₁⟩ ⟨w₂⟩ _
      fun t₃ S' ψ ⟨b₁⟩ ⟨b₂⟩ ⟨g⟩ ↦ ?_)
    have e1 : mp F ψ (mp F w₁ (s t₁ a₁)) = mp F g (s t₃ (a₁ ≫ b₁)) := by
      rw [hs t₁ t₃ a₁ b₁ h₁, ← mp_comp]
      change _ = mp F g (mp F (G.map b₁) _)
      rw [← mp_comp F (G.map b₁) g, Subsingleton.elim (G.map b₁ ≫ g) (w₁ ≫ ψ)]
    have e2 : mp F ψ (mp F w₂ (s t₂ a₂)) = mp F g (s t₃ (a₂ ≫ b₂)) := by
      rw [hs t₂ t₃ a₂ b₂ h₂, ← mp_comp]
      change _ = mp F g (mp F (G.map b₂) _)
      rw [← mp_comp F (G.map b₂) g, Subsingleton.elim (G.map b₂ ≫ g) (w₂ ≫ ψ)]
    have e3 : a₁ ≫ b₁ = a₂ ≫ b₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov
  have hex : ∀ S (u : G.obj t ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t' : C') (a : t ⟶ t') (w : G.obj t' ⟶ S), Sg t' a ∧ mp F w (s t' a) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t', a, ha, ⟨w⟩⟩ := hb' i S u hi
      exact ⟨mp F w (s t' a), fun _ ↦ ⟨t', a, w, ha, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t₁, a₁, w₁, h₁, e₁⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi.map _
    obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
    rw [← e₁, ← e₂, ← mp_comp]
    exact key _ _ _ _ h₂ h₁ _ _ _
  refine ⟨x, fun t' a ha ↦ ?_⟩
  change mp F (G.map a) x = s t' a
  refine sub_eq_zero.1 (sep_std H (Basis.span_map_eq_top F (G.map a) hb) _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (G.map a ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (G.map a ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e₂, key t₂ t' a₂ a h₂ ha S' w₂ ψ, sub_self]
end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
