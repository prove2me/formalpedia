-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Glue.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:02.545817+00:00
-- url     : https://prove2.me/submissions/7100d8d2-6022-4d72-b893-b82b66ce2c31

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
include hPQ sep
namespace GlobalTheory.CatCoh.Desc
namespace Glue
theorem _root_.solution (h : Glue F P) : Glue F Q := by
  intro s hs
  obtain ⟨x, hx⟩ := h s fun S S' u ψ hp ↦ hs S S' u ψ (hPQ S u hp)
  refine ⟨x, fun S u hq ↦ sub_eq_zero.1 (sep S u hq _ fun S' ψ hp ↦ ?_)⟩
  rw [map_sub, ← mp_comp, hx _ _ hp, hs _ _ _ _ hq, sub_self]
end Glue
end GlobalTheory.CatCoh.Desc
