-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.pull_restrict_small_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:23.175211+00:00
-- url     : https://prove2.me/submissions/3544788e-b5c2-4044-8c1b-968e8b9fe056

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective


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
open Classical
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (sep : ∀ T, Sep F fun S (_ : T ⟶ S) ↦ P S) (glue : ∀ T, Glue F fun S (_ : T ⟶ S) ↦ P S)
    (van : ∀ T, Van1 F fun S (_ : T ⟶ S) ↦ P S) :
    Function.Injective (CoefMap.restrict F P.ι).pull2 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨f, hf⟩ := hc
  obtain ⟨h, hh⟩ := coboundary_of_restrict F (E := fun _ ↦ PUnit.{1}) (fun e _ ↦ e) (fun _ _ _ ↦ rfl)
    (fun _ _ ↦ True) (fun S _ ↦ P S) (fun _ _ _ _ _ ↦ trivial) (fun S _ _ ↦ sep S)
    (fun S _ _ ↦ glue S) (fun S _ _ ↦ van S) (fun S S' S'' _ ψ χ ↦ z.1 S S' S'' ψ χ)
    (fun _ _ _ _ _ ψ χ ω _ ↦ z.2 ψ χ ω)
    (fun S S' _ ψ ↦ if h : P S then f ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0)
    fun S S' S'' _ ψ χ hp ↦ by
      simp only [dif_pos hp, dif_pos (hP _ _ ψ hp)]
      exact congrFun (congrFun (congrFun (congrFun (congrFun hf ⟨S, hp⟩) ⟨S', hP _ _ ψ hp⟩)
        ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩) (ObjectProperty.homMk ψ)) (ObjectProperty.homMk χ)
  refine H2.mk_eq_zero.2 ⟨fun S S' ψ ↦ h S S' PUnit.unit ψ, ?_⟩
  funext S S' S'' ψ χ
  exact hh S S' S'' PUnit.unit ψ χ trivial
end GlobalTheory.CatCoh.Desc
