-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.IsSec.kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:28.903828+00:00
-- url     : https://prove2.me/submissions/049cf29d-f5de-4277-a11c-21b8e20ff7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_IsSec_frac

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
theorem _root_.solution (c : F.obj T) {s : ∀ S, (T ⟶ S) → F.obj S} (hs : IsSec F P s)
    (h0 : ∀ S u, P S u → IsUnit (mp F u c) → s S u = 0) :
    ∀ᶠ M : ℕ in atTop, ∀ S u, P S u → mp F u c ^ M * s S u = 0 := by
  obtain ⟨n, x, e⟩ := hs.frac H hP
  obtain ⟨T', l, h1, -, h3, -⟩ := H T (b * c)
  rw [map_mul, IsUnit.mul_iff] at h1
  obtain ⟨m, hm⟩ := h3 x (by rw [← e _ _ ((hP _ _).2 h1.1), h0 _ _ ((hP _ _).2 h1.1) h1.2, zero_mul])
  refine eventually_atTop.2 ⟨m, fun N hN S u h ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have := congrArg (mp F u) hm
  rw [map_mul, map_pow, map_mul, map_zero, ← e S u h] at this
  refine ((((hP _ _).1 h).pow (m + n)).mul_right_eq_zero).1 ?_
  linear_combination mp F u c ^ k * this
end IsSec
end GlobalTheory.CatCoh.Desc
