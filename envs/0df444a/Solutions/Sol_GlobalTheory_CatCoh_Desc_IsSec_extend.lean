-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.IsSec.extend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:28.772236+00:00
-- url     : https://prove2.me/submissions/de833339-3407-4959-b13f-c7410e295238

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
theorem _root_.solution (c : F.obj T) {s : ∀ S, (T ⟶ S) → F.obj S}
    (hs : IsSec F (fun S u ↦ P S u ∧ IsUnit (mp F u c)) s) :
    ∀ᶠ N : ℕ in atTop, ∃ s', IsSec F P s' ∧
      ∀ S u, P S u → IsUnit (mp F u c) → s' S u = mp F u c ^ N * s S u := by
  obtain ⟨n, x, e⟩ := hs.frac H (b := b * c) fun S u ↦ by rw [hP, map_mul, IsUnit.mul_iff]
  refine eventually_atTop.2 ⟨n, fun N hN ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨fun S u ↦ mp F u x * Ring.inverse (mp F u b) ^ n * mp F u c ^ m, fun S S' u ψ h ↦ ?_,
    fun S u h h' ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (hP _ _).1 h
    have : Ring.inverse (mp F ψ y) = mp F ψ (Ring.inverse y) := by
      rw [Ring.inverse_unit]
      exact Ring.inverse_unit (Units.map (mp F ψ : F.obj S →* F.obj S') y)
    simp only [mp_comp, map_mul, map_pow, ← hy, this]
  · have k := Ring.mul_inverse_cancel _ ((hP _ _).1 h)
    have k' : mp F u b ^ n * Ring.inverse (mp F u b) ^ n = 1 := by rw [← mul_pow, k, one_pow]
    beta_reduce
    rw [← e S u ⟨h, h'⟩, map_mul]
    linear_combination (s S u * mp F u c ^ (n + m)) * k'
end IsSec
end GlobalTheory.CatCoh.Desc
