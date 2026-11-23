-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.isUnit_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:31.632699+00:00
-- url     : https://prove2.me/submissions/5028e39f-aa57-4546-b3ea-28a63878e0d0

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
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
omit [Fintype ι]
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution {S S' : C} {u : T ⟶ S} (ψ : S ⟶ S') {x : F.obj T} (h : IsUnit (mp F u x)) :
    IsUnit (mp F (u ≫ ψ) x) := by
  rw [mp_comp]; exact h.map _
end GlobalTheory.CatCoh.Desc
