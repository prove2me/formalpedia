-- Prove2me | solution 1 for HiltonMilner.meet_erase_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:07:44.798369+00:00
-- url     : https://prove2.me/submissions/9550e2c9-4508-4f88-8a91-f20940d8a038

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Theorems.Thm_HiltonMilner_shift_mem_of_fixed

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} {z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ)
    (hfix : ∀ y ∈ X.erase z, sh y z ℬ = ℬ) {A B : Finset ℕ} (hA : A ∈ 𝒜) (hB : B ∈ ℬ)
    (hzA : z ∈ A) (hzB : z ∈ B) (hcard : #(A ∪ B) < #X) :
    (A.erase z ∩ B.erase z).Nonempty := by
  by_contra hdis
  rw [not_nonempty_iff_eq_empty] at hdis
  obtain ⟨y, hyX, hyAB⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hyz : y ≠ z := fun e => hyAB (e ▸ mem_union_left _ hzA)
  have hyB : y ∉ B := fun h => hyAB (mem_union_right _ h)
  have hyA : y ∉ A := fun h => hyAB (mem_union_left _ h)
  have hB' := shift_mem_of_fixed (hfix y (mem_erase.2 ⟨hyz, hyX⟩)) hB hyB hzB
  obtain ⟨u, hu⟩ := h A hA _ hB'
  rw [mem_inter, mem_insert, mem_erase] at hu
  rcases hu.2 with rfl | ⟨huz, huB⟩
  · exact hyA hu.1
  · have : u ∈ A.erase z ∩ B.erase z :=
      mem_inter.2 ⟨mem_erase.2 ⟨huz, hu.1⟩, mem_erase.2 ⟨huz, huB⟩⟩
    rw [hdis] at this; simp at this
end HiltonMilner
