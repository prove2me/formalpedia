-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Van1.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:02.591845+00:00
-- url     : https://prove2.me/submissions/c1fada10-b29e-4c2d-8ecd-cd0300aed9f4

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
variable {F} {T : C} {P Q : ∀ S, (T ⟶ S) → Prop} (hPQ : ∀ S u, P S u → Q S u)
  (hQ : ∀ S S' u (ψ : S ⟶ S'), Q S u → Q S' (u ≫ ψ))
  (sep : ∀ S u, Q S u → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (glue : ∀ S u, Q S u → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (van : ∀ S u, Q S u → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
include hPQ hQ sep glue
namespace GlobalTheory.CatCoh.Desc
namespace Van1
theorem _root_.solution (h : Van1 F P) : Van1 F Q := by
  intro a ha
  obtain ⟨b, hb⟩ := h a fun S S' S'' u ψ χ hp ↦ ha S S' S'' u ψ χ (hPQ S u hp)
  have h1 : ∀ S (u : T ⟶ S), ∃ x : F.obj S, Q S u → ∀ S' (ψ : S ⟶ S'), P S' (u ≫ ψ) →
      mp F ψ x = b S' (u ≫ ψ) - a S S' u ψ := by
    intro S u
    by_cases hq : Q S u
    · obtain ⟨x, hx⟩ := glue S u hq (fun S' ψ ↦ b S' (u ≫ ψ) - a S S' u ψ) fun S' S'' ψ χ hp ↦ by
        have k1 := ha _ _ _ u ψ χ hq
        have k2 := hb _ _ (u ≫ ψ) χ hp
        simp only [map_sub, Category.assoc] at k2 ⊢
        linear_combination k2 - k1
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose x hx using h1
  refine ⟨x, fun S S' u ψ hq ↦ sub_eq_zero.1 (sep S' _ (hQ _ _ u ψ hq) _ fun S'' χ hp ↦ ?_)⟩
  have k1 := ha _ _ _ u ψ χ hq
  have k2 := hx _ _ (hQ _ _ u ψ hq) _ χ hp
  have k3 := hx _ _ hq _ (ψ ≫ χ) (by rwa [← Category.assoc])
  simp only [map_sub, Category.assoc, mp_comp] at k2 k3 ⊢
  linear_combination k2 - k3 + k1
end Van1
end GlobalTheory.CatCoh.Desc
