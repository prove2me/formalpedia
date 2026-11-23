-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.coboundary_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:31.503155+00:00
-- url     : https://prove2.me/submissions/5e41821b-f696-4295-9b7c-f32fa34d27c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution {E : C → Type w} (act : ∀ {S S'}, E S → (S ⟶ S') → E S')
    (hact : ∀ {S S' S''} (e : E S) (ψ : S ⟶ S') (χ : S' ⟶ S''), act e (ψ ≫ χ) = act (act e ψ) χ)
    (Q P : ∀ S, E S → Prop) (hQ : ∀ S S' e (ψ : S ⟶ S'), Q S e → Q S' (act e ψ))
    (sep : ∀ S e, Q S e → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (glue : ∀ S e, Q S e → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (van : ∀ S e, Q S e → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (z : ∀ S S' S'', E S → (S ⟶ S') → (S' ⟶ S'') → F.obj S'')
    (hz : ∀ S S' S'' S''' e ψ χ ω, Q S e → mp F ω (z S S' S'' e ψ χ) + z S S'' S''' e (ψ ≫ χ) ω =
      z S S' S''' e ψ (χ ≫ ω) + z S' S'' S''' (act e ψ) χ ω)
    (f : ∀ S S', E S → (S ⟶ S') → F.obj S')
    (hf : ∀ S S' S'' e ψ χ, P S e →
      mp F χ (f S S' e ψ) - f S S'' e (ψ ≫ χ) + f S' S'' (act e ψ) χ = z S S' S'' e ψ χ) :
    ∃ h : ∀ S S', E S → (S ⟶ S') → F.obj S', ∀ S S' S'' e ψ χ, Q S e →
      mp F χ (h S S' e ψ) - h S S'' e (ψ ≫ χ) + h S' S'' (act e ψ) χ = z S S' S'' e ψ χ := by
  have h1 : ∀ T (e : E T), ∃ g : ∀ S, (T ⟶ S) → F.obj S, Q T e → ∀ S S' u ψ, P S (act e u) →
      g S' (u ≫ ψ) - mp F ψ (g S u) = f S S' (act e u) ψ - z T S S' e u ψ := by
    intro T e
    by_cases hq : Q T e
    · obtain ⟨g, hg⟩ := van T e hq (fun S S' u ψ ↦ f S S' (act e u) ψ - z T S S' e u ψ)
        fun S S' S'' u ψ χ hp ↦ by
          have k1 := hz _ _ _ _ e u ψ χ hq
          have k2 := hf _ _ _ _ ψ χ hp
          simp only [map_sub, hact]
          linear_combination k1 - k2
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose g hg using h1
  have h2 : ∀ T T' (e : E T) (φ : T ⟶ T'), ∃ x : F.obj T', Q T e → ∀ S (u : T' ⟶ S),
      P S (act (act e φ) u) →
      mp F u x = z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u := by
    intro T T' e φ
    by_cases hq : Q T e
    · obtain ⟨x, hx⟩ := glue T' _ (hQ _ _ e φ hq)
        (fun S u ↦ z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u) fun S S' u ψ hp ↦ by
          have k1 := hz _ _ _ _ e φ u ψ hq
          have k2 := hg T e hq S S' (φ ≫ u) ψ (by rwa [hact])
          have k3 := hg T' _ (hQ _ _ e φ hq) S S' u ψ hp
          simp only [map_sub, map_add, hact, Category.assoc] at k2 ⊢
          linear_combination k2 - k1 - k3
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose h hh using h2
  refine ⟨h, fun T T' T'' e φ ψ hq ↦ sub_eq_zero.1 (sep T'' _ (hQ _ _ _ ψ (hQ _ _ e φ hq)) _
    fun S u hp ↦ ?_)⟩
  have k1 := hz _ _ _ _ e φ ψ u hq
  have k2 := hh T T' e φ hq S (ψ ≫ u) (by rwa [hact])
  have k3 := hh T T'' e (φ ≫ ψ) hq S u (by rwa [hact])
  have k4 := hh T' T'' _ ψ (hQ _ _ e φ hq) S u hp
  simp only [map_sub, map_add, hact, Category.assoc, mp_comp] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1
end GlobalTheory.CatCoh.Desc
