-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Van2.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:03.200034+00:00
-- url     : https://prove2.me/submissions/97fe28fc-bc09-4cc8-aa81-cf98d36a53da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_coboundary_of_restrict

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
include hPQ hQ sep glue van
namespace GlobalTheory.CatCoh.Desc
namespace Van2
theorem _root_.solution (h : Van2 F P) : Van2 F Q := by
  intro z hz
  obtain ⟨f, hf⟩ := h z fun S S' S'' S''' u ψ χ ω hp ↦ hz S S' S'' S''' u ψ χ ω (hPQ S u hp)
  exact coboundary_of_restrict F (E := fun S ↦ T ⟶ S) (fun u ψ ↦ u ≫ ψ)
    (fun _ _ _ ↦ (Category.assoc _ _ _).symm) Q P hQ sep glue van z hz f hf
end Van2
end GlobalTheory.CatCoh.Desc
