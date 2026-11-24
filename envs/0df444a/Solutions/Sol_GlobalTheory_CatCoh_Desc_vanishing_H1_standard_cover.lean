-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.vanishing_H1_standard_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:24.057883+00:00
-- url     : https://prove2.me/submissions/978f065b-be9c-496d-b951-10bc0f49fa97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_vanishing_H1_inverting_morphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_cech1
import Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp

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
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
open Classical
include H hb
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : Van1 F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro a ha
  choose β hβ using fun i ↦ vanishing_H1_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) a
    fun S S' S'' u ψ χ h ↦ ha S S' S'' u ψ χ ⟨i, h⟩
  obtain ⟨e, he, he'⟩ := cech1 H hb (fun i j S u ↦ β j S u - β i S u)
    (fun i j S S' u ψ h ↦ by
      rw [map_sub]
      linear_combination hβ j S S' u ψ h.2 - hβ i S S' u ψ h.1)
    (fun _ _ _ _ _ _ _ _ ↦ by ring)
  obtain ⟨γ, hγ⟩ : ∃ γ : ∀ S, (T ⟶ S) → F.obj S, ∀ i S u, IsUnit (mp F u (b i)) →
      γ S u = β i S u - e i S u := by
    refine ⟨fun S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then β h.choose S u - e h.choose S u else 0,
      fun i S u hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination he' i _ S u hi h.choose_spec
  refine ⟨γ, fun S S' u ψ ⟨i, hi⟩ ↦ ?_⟩
  rw [hγ i _ _ hi, hγ i _ _ (isUnit_comp ψ hi), he i _ _ _ _ hi, map_sub]
  linear_combination hβ i S S' u ψ hi
end GlobalTheory.CatCoh.Desc
