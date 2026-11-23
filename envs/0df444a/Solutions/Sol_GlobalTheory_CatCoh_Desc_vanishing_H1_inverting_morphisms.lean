-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.vanishing_H1_inverting_morphisms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:44.124466+00:00
-- url     : https://prove2.me/submissions/eb4a215a-fd98-4894-bf43-ad3b78aecfb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_exists_initial

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
variable {F} (H : HasLoc F) {T : C} {P : ∀ S, (T ⟶ S) → Prop} {b : F.obj T}
  (hP : ∀ S u, P S u ↔ IsUnit (mp F u b))
open Classical
include H hP
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : Van1 F P := by
  obtain ⟨T', l, p, hl, h1, h2⟩ := exists_initial H hP
  intro a ha
  refine ⟨fun S u ↦ if h : P S u then a T' S l (p S u h) else 0, fun S S' u ψ h ↦ ?_⟩
  obtain ⟨h', e⟩ := h2 S S' u ψ h
  simp only [dif_pos h, dif_pos h', e]
  rw [ha _ _ _ _ _ _ hl, h1, add_sub_cancel_left]
end GlobalTheory.CatCoh.Desc
