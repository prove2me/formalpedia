-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.IsSec.frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:30.641313+00:00
-- url     : https://prove2.me/submissions/c62db4f7-a542-4cb0-b8bd-d2bd47986274

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
namespace IsSec
theorem _root_.solution {s : ∀ S, (T ⟶ S) → F.obj S} (hs : IsSec F P s) :
    ∃ (n : ℕ) (x : F.obj T), ∀ S u, P S u → s S u * mp F u b ^ n = mp F u x := by
  obtain ⟨T', l, h1, h2, -, h4⟩ := H T b
  obtain ⟨n, x, e⟩ := h2 (s T' l)
  refine ⟨n, x, fun S u h ↦ ?_⟩
  obtain ⟨v, rfl, -⟩ := h4 S u ((hP _ _).1 h)
  rw [hs _ _ _ _ ((hP _ _).2 h1), mp_comp, mp_comp, ← e, map_mul, map_pow]
end IsSec
end GlobalTheory.CatCoh.Desc
