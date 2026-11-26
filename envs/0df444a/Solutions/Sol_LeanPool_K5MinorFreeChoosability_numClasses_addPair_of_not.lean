-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_addPair_of_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:57.732206+00:00
-- url     : https://prove2.me/submissions/cd6b4cf1-4704-4369-bc03-cb15cd1a4cab

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
private theorem injOn_lift_addPair (s : Setoid α) (x y : α) :
    Set.InjOn (Quotient.lift (fun a => Quotient.mk (addPairSetoid s x y) a)
      (fun _ _ hab => Quotient.sound (Or.inl hab)) : Quotient s → _)
      {q | q ≠ Quotient.mk s y} := by
  intro p hp q hq hpq
  induction p using Quotient.inductionOn with
  | h a =>
  induction q using Quotient.inductionOn with
  | h b =>
  simp only [Set.mem_ofPred_eq, ne_eq] at hp hq
  have hab : addPairSetoid s x y a b := Quotient.exact hpq
  rcases hab with h | ⟨_, h2⟩ | ⟨h1, _⟩
  · exact Quotient.sound h
  · exact absurd (Quotient.sound (s.symm h2)) hq
  · exact absurd (Quotient.sound h1) hp
variable [DecidableEq α]
end LeanPool.K5MinorFreeChoosability
end
end

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] {s : Setoid α} {x y : α} (hxy : ¬ s x y) :
    numClasses s = numClasses (addPairSetoid s x y) + 1 := by
  classical
  have := Fintype.ofFinite α
  set f := (Quotient.lift (fun a => Quotient.mk (addPairSetoid s x y) a)
      (fun a b hab => Quotient.sound (Or.inl hab)) : Quotient s → _) with hf
  have hinj : Set.InjOn f ↑(Finset.univ.erase (Quotient.mk s y)) := by
    intro p hp q hq hpq
    exact injOn_lift_addPair s x y (by simpa using hp) (by simpa using hq) hpq
  have himg : (Finset.univ.erase (Quotient.mk s y)).image f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
    rw [Finset.mem_image]
    by_cases ha : Quotient.mk s a = Quotient.mk s y
    · refine ⟨Quotient.mk s x, ?_, ?_⟩
      · rw [Finset.mem_erase]
        exact ⟨fun h => hxy (Quotient.exact h), Finset.mem_univ _⟩
      · have hay : s a y := Quotient.exact ha
        exact Quotient.sound (Or.inr (Or.inl ⟨s.refl x, s.symm hay⟩))
    · exact ⟨Quotient.mk s a, Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩, rfl⟩
  have h1 := Finset.card_image_of_injOn hinj
  rw [himg, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ] at h1
  have hpos : 0 < Fintype.card (Quotient s) :=
    Fintype.card_pos_iff.2 ⟨Quotient.mk s x⟩
  simp only [numClasses, Nat.card_eq_fintype_card]
  omega
end LeanPool.K5MinorFreeChoosability
