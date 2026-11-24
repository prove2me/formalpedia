-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.descent_H2_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:22.29653+00:00
-- url     : https://prove2.me/submissions/1505c698-3ffb-4f5b-a329-72f7c532675b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
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
    (van : ∀ T, Van1 F fun S (_ : T ⟶ S) ↦ P S) (van2 : ∀ T, Van2 F fun S (_ : T ⟶ S) ↦ P S) :
    Function.Surjective (CoefMap.restrict F P.ι).pull2 := by
  intro c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨z, hz, hy⟩ : ∃ z : C2 F, (∀ S S' S'' S''' ψ χ ω, P S →
      mp F ω (z S S' S'' ψ χ) + z S S'' S''' (ψ ≫ χ) ω = z S S' S''' ψ (χ ≫ ω) + z S' S'' S''' χ ω) ∧
      ∀ S S' S'' ψ χ, y.1 S S' S'' ψ χ = z S.obj S'.obj S''.obj ψ.hom χ.hom := by
    refine ⟨fun S S' S'' ψ χ ↦ if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ ⟨S'', hP _ _ χ (hP _ _ ψ h)⟩
      (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ) else 0, fun S S' S'' S''' ψ χ ω hp ↦ ?_,
      fun S S' S'' ψ χ ↦ ?_⟩
    · simp only [dif_pos hp, dif_pos (hP _ _ ψ hp)]
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hP _ _ ψ hp⟩) (T'' := ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩)
        (T''' := ⟨S''', hP _ _ ω (hP _ _ χ (hP _ _ ψ hp))⟩) (ObjectProperty.homMk ψ)
        (ObjectProperty.homMk χ) (ObjectProperty.homMk ω)
    · simp only [dif_pos S.property]
      rfl
  have h1 : ∀ T, ∃ a : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', (∀ S S' S'' u ψ χ, P S →
      mp F χ (a S S' u ψ) - a S S'' u (ψ ≫ χ) + a S' S'' (u ≫ ψ) χ = z S S' S'' ψ χ) ∧
      (P T → a = z T) := by
    intro T
    by_cases hp : P T
    · exact ⟨z T, fun S S' S'' u ψ χ _ ↦ by linear_combination hz _ _ _ _ u ψ χ hp, fun _ ↦ rfl⟩
    · obtain ⟨a, ha⟩ := van2 T (fun S S' S'' _ ψ χ ↦ z S S' S'' ψ χ)
        fun _ _ _ _ _ ψ χ ω h ↦ hz _ _ _ _ ψ χ ω h
      exact ⟨a, ha, fun h ↦ absurd h hp⟩
  choose a ha ha' using h1
  have h2 : ∀ T T' (φ : T ⟶ T'), ∃ b : ∀ S, (T' ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
      b S' (u ≫ ψ) - mp F ψ (b S u) = a T S S' (φ ≫ u) ψ - a T' S S' u ψ) ∧
      (P T → ∀ S u, b S u = z T T' S φ u) := by
    intro T T' φ
    by_cases hp : P T
    · refine ⟨fun S u ↦ z T T' S φ u, fun S S' u ψ _ ↦ ?_, fun _ _ _ ↦ rfl⟩
      rw [ha' T hp, ha' T' (hP _ _ φ hp)]
      linear_combination -hz _ _ _ _ φ u ψ hp
    · obtain ⟨b, hb⟩ := van T' (fun S S' u ψ ↦ a T S S' (φ ≫ u) ψ - a T' S S' u ψ)
        fun S S' S'' u ψ χ h ↦ by
          have k1 := ha T _ _ _ (φ ≫ u) ψ χ h
          have k2 := ha T' _ _ _ u ψ χ h
          simp only [map_sub, Category.assoc] at k1 ⊢
          linear_combination k2 - k1
      exact ⟨b, hb, fun h ↦ absurd h hp⟩
  choose b hb hb' using h2
  have h3 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), ∃ x : F.obj T'', ∀ S (u : T'' ⟶ S), P S →
      mp F u x = b T T' φ S (ψ ≫ u) + b T' T'' ψ S u - b T T'' (φ ≫ ψ) S u := by
    intro T T' T'' φ ψ
    refine glue T'' _ fun S S' u χ hp ↦ ?_
    have k1 := hb T T' φ _ _ (ψ ≫ u) χ hp
    have k2 := hb T' T'' ψ _ _ u χ hp
    have k3 := hb T T'' (φ ≫ ψ) _ _ u χ hp
    simp only [map_sub, map_add, Category.assoc] at k1 k3 ⊢
    linear_combination k1 + k2 - k3
  choose c hc using h3
  refine ⟨H2.mk F ⟨c, fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun S u hp ↦ ?_)⟩, ?_⟩
  · have k1 := hc _ _ _ φ ψ S (χ ≫ u) hp
    have k2 := hc _ _ _ (φ ≫ ψ) χ S u hp
    have k3 := hc _ _ _ φ (ψ ≫ χ) S u hp
    have k4 := hc _ _ _ ψ χ S u hp
    simp only [map_sub, map_add, Category.assoc, mp_comp] at k1 k2 k3 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class]
    congr 1
    refine Subtype.ext ?_
    funext S S' S'' ψ χ
    have k1 := hc _ _ _ ψ.hom χ.hom _ (𝟙 _) S''.property
    have k2 := hz _ _ _ _ ψ.hom χ.hom (𝟙 _) S.property
    rw [hb' _ _ _ S.property, hb' _ _ _ S.property, hb' _ _ _ S'.property, mp_id] at k1
    rw [mp_id] at k2
    rw [hy]
    change c _ _ _ ψ.hom χ.hom = _
    linear_combination k1 - k2
end GlobalTheory.CatCoh.Desc
