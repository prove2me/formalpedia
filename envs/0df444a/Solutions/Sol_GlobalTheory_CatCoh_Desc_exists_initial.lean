-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.exists_initial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:31.459128+00:00
-- url     : https://prove2.me/submissions/154d4911-3af3-4381-bc3e-5e6a5bfdc588

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
variable {F} (H : HasLoc F) {T : C} {P : ∀ S, (T ⟶ S) → Prop} {b : F.obj T}
  (hP : ∀ S u, P S u ↔ IsUnit (mp F u b))
include H hP
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : ∃ (T' : C) (l : T ⟶ T') (p : ∀ S (u : T ⟶ S), P S u → (T' ⟶ S)), P T' l ∧
    (∀ S u h, l ≫ p S u h = u) ∧
    ∀ S S' u (ψ : S ⟶ S') h, ∃ h', p S' (u ≫ ψ) h' = p S u h ≫ ψ := by
  obtain ⟨T', l, h1, -, -, h4⟩ := H T b
  choose p hp hp' using h4
  refine ⟨T', l, fun S u h ↦ p S u ((hP _ _).1 h), (hP _ _).2 h1, fun S u h ↦ hp _ _ _,
    fun S S' u ψ h ↦ ⟨(hP _ _).2 ?_, (hp' _ _ _ _ ?_).symm⟩⟩
  · rw [mp_comp]; exact ((hP _ _).1 h).map _
  · beta_reduce
    rw [← Category.assoc, hp]
end GlobalTheory.CatCoh.Desc
