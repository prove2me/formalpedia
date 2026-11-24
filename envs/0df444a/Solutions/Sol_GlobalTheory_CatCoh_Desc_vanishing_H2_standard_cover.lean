-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.vanishing_H2_standard_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:28.820798+00:00
-- url     : https://prove2.me/submissions/548e2d3b-a875-49cc-af0e-243b8a9eb1d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_vanishing_H1_inverting_morphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_vanishing_H2_inverting_morphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_cech2
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
theorem _root_.solution : Van2 F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro z hz
  choose a ha using fun i ↦ vanishing_H2_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) z
    fun S S' S'' S''' u ψ χ ω h ↦ hz S S' S'' S''' u ψ χ ω ⟨i, h⟩
  choose β hβ using fun i j ↦ vanishing_H1_inverting_morphisms H
    (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
    (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (fun S S' u ψ ↦ a j S S' u ψ - a i S S' u ψ)
    fun S S' S'' u ψ χ h ↦ by
      rw [map_sub]
      linear_combination ha i S S' S'' u ψ χ h.1 - ha j S S' S'' u ψ χ h.2
  obtain ⟨e, he, he'⟩ := cech2 H hb (fun i j k S u ↦ β j k S u - β i k S u + β i j S u)
    (fun i j k S S' u ψ h ↦ by
      rw [map_add, map_sub]
      linear_combination hβ j k S S' u ψ ⟨h.1.2, h.2⟩ - hβ i k S S' u ψ ⟨h.1.1, h.2⟩ +
        hβ i j S S' u ψ h.1)
    (fun _ _ _ _ _ _ _ _ _ _ ↦ by ring)
  obtain ⟨γ, hγ⟩ : ∃ γ : ι → ∀ S, (T ⟶ S) → F.obj S, ∀ i j S u, IsUnit (mp F u (b i)) →
      IsUnit (mp F u (b j)) → γ j S u - γ i S u = β i j S u - e i j S u := by
    refine ⟨fun i S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then
      β h.choose i S u - e h.choose i S u else 0, fun i j S u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j S u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', ∀ i S S' u ψ, IsUnit (mp F u (b i)) →
      α S S' u ψ = a i S S' u ψ - (γ i S' (u ≫ ψ) - mp F ψ (γ i S u)) := by
    refine ⟨fun S S' u ψ ↦ if h : ∃ i, IsUnit (mp F u (b i)) then
      a h.choose S S' u ψ - (γ h.choose S' (u ≫ ψ) - mp F ψ (γ h.choose S u)) else 0,
      fun i S S' u ψ hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F ψ) (hγ i _ S u hi h.choose_spec)
    have k2 := hγ i _ S' (u ≫ ψ) (isUnit_comp ψ hi) (isUnit_comp ψ h.choose_spec)
    have k3 := he i _ S S' u ψ ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ S S' u ψ ⟨hi, h.choose_spec⟩
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun S S' S'' u ψ χ ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (isUnit_comp ψ hi)]
  simp only [map_sub, mp_comp, Category.assoc]
  linear_combination ha i S S' S'' u ψ χ hi
end GlobalTheory.CatCoh.Desc
