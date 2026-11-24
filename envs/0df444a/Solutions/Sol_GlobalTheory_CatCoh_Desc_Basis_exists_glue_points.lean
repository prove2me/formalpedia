-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Basis.exists_glue_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:39:30.00972+00:00
-- url     : https://prove2.me/submissions/ccc72e64-cfc6-4d0d-bf30-9d0af5cfe861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_span_map_eq_top
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_std
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']
namespace GlobalTheory.CatCoh.Desc.Basis
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (t₁ t₂ : C') (s : ∀ t, F.obj (G.obj t))
    (hs : ∀ t t' (a : t ⟶ t'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → s t' = mp F (G.map a) (s t)) :
    ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ (x S) = mp F w (s t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
        x S' = mp F ψ (x S)) := by
  have key : ∀ t t' (S : C) (w : G.obj t ⟶ S) (w' : G.obj t' ⟶ S), Nonempty (t₁ ⟶ t) →
      Nonempty (t₂ ⟶ t) → Nonempty (t₁ ⟶ t') → Nonempty (t₂ ⟶ t') →
      mp F w (s t) = mp F w' (s t') := by
    intro t t' S w w' h1 h2 h1' h2'
    refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w⟩ ⟨w'⟩ _ fun t'' S' ψ ⟨a⟩ ⟨a'⟩ ⟨w''⟩ ↦ ?_)
    have e1 : w ≫ ψ = G.map a ≫ w'' := Subsingleton.elim _ _
    have e2 : w' ≫ ψ = G.map a' ≫ w'' := Subsingleton.elim _ _
    rw [map_sub, ← mp_comp, ← mp_comp, e1, e2, mp_comp, mp_comp, ← hs t t'' a h1 h2,
      ← hs t' t'' a' h1' h2', sub_self]
  classical
  let σ : ∀ S, F.obj S := fun S ↦
    if h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) then
      mp F h.choose_spec.2.2.some (s h.choose) else 0
  have hσ : ∀ t S (w : G.obj t ⟶ S), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      σ S = mp F w (s t) := by
    intro t S w h1 h2
    have h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) :=
      ⟨t, h1, h2, ⟨w⟩⟩
    simp only [σ, dif_pos h]
    exact key _ _ _ _ _ h.choose_spec.1 h.choose_spec.2.1 h1 h2
  have h1 : ∀ S, ∃ x : F.obj S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ x = mp F w (s t) := by
    intro S
    by_cases hS : Nonempty (G.obj t₁ ⟶ S) ∧ Nonempty (G.obj t₂ ⟶ S)
    · obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := hS
      obtain ⟨n, b, hb, hcov⟩ := hdir t₁ t₂ S w₁ w₂
      obtain ⟨x, hx⟩ := glue_std H hb (fun S' _ ↦ σ S') fun S' S'' ψ χ ⟨i, hi⟩ ↦ by
        obtain ⟨t, h1, h2, ⟨w⟩⟩ := hcov i S' ψ hi
        show σ S'' = mp F χ (σ S')
        rw [hσ t S'' (w ≫ χ) h1 h2, hσ t S' w h1 h2, mp_comp]
      refine ⟨x, fun _ _ t S' ψ w h1 h2 ↦
        sub_eq_zero.1 <| sep_std H (span_map_eq_top F ψ hb) _ fun S'' χ ⟨i, hi⟩ ↦ ?_⟩
      have hi' : IsUnit (mp F (ψ ≫ χ) (b i)) := by rw [mp_comp]; exact hi
      rw [map_sub, ← mp_comp, hx S'' (ψ ≫ χ) ⟨i, hi'⟩, ← mp_comp, hσ t S'' (w ≫ χ) h1 h2,
        sub_self]
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hS⟩
  choose x hx using h1
  refine ⟨x, hx, fun S S' ψ h1 h2 ↦ ?_⟩
  obtain ⟨w₁⟩ := h1
  obtain ⟨w₂⟩ := h2
  refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ _ fun t S'' χ h1' h2' ⟨w⟩ ↦ ?_)
  rw [map_sub, hx S' ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ t S'' χ w h1' h2', ← mp_comp,
    hx S ⟨w₁⟩ ⟨w₂⟩ t S'' (ψ ≫ χ) w h1' h2', sub_self]
end GlobalTheory.CatCoh.Desc.Basis
