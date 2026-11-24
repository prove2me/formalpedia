-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.acyclic_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:49.116341+00:00
-- url     : https://prove2.me/submissions/5e3d7f25-0bbf-476f-a8e9-c520bab1c61b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Glue_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van1_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van2_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_std
import Theorems.Thm_GlobalTheory_CatCoh_Desc_vanishing_H1_standard_cover
import Theorems.Thm_GlobalTheory_CatCoh_Desc_vanishing_H2_standard_cover

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
theorem _root_.solution (H : HasLoc F) (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (cov : ∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → P S) (T : C) :
    (Sep F fun S (_ : T ⟶ S) ↦ P S) ∧ (Glue F fun S (_ : T ⟶ S) ↦ P S) ∧
      (Van1 F fun S (_ : T ⟶ S) ↦ P S) ∧ Van2 F fun S (_ : T ⟶ S) ↦ P S := by
  obtain ⟨n, b, hb, h⟩ := cov T
  have hPQ : ∀ S (u : T ⟶ S), (∃ i, IsUnit (mp F u (b i))) → P S := fun S u ⟨i, hi⟩ ↦ h i S u hi
  have hQ : ∀ S S' (_ : T ⟶ S) (ψ : S ⟶ S'), P S → P S' := fun S S' _ ψ ↦ hP S S' ψ
  have hb' : ∀ S (u : T ⟶ S), Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := fun S u ↦ by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  have sep : ∀ S (u : T ⟶ S), P S →
      Sep F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using sep_std H (hb' S u)
  have glue : ∀ S (u : T ⟶ S), P S →
      Glue F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using glue_std H (hb' S u)
  have van : ∀ S (u : T ⟶ S), P S →
      Van1 F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using vanishing_H1_standard_cover H (hb' S u)
  exact ⟨(sep_std H hb).mono hPQ, (glue_std H hb).mono hPQ sep,
    (vanishing_H1_standard_cover H hb).mono hPQ hQ sep glue, (vanishing_H2_standard_cover H hb).mono hPQ hQ sep glue van⟩
end GlobalTheory.CatCoh.Desc
