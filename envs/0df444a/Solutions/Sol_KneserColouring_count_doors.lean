-- Prove2me | solution 1 for KneserColouring.count_doors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:34.826003+00:00
-- url     : https://prove2.me/submissions/d6e046a3-46fd-4278-891f-9c64e9837000

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Theorems.Thm_KneserColouring_NoComp_mono
public import Theorems.Thm_KneserColouring_count_isAlt_erase
public import Theorems.Thm_KneserColouring_image_erase_eq_of_dup

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {α : Type*} [DecidableEq α] (s : Finset α) (ℓ : α → ℤ) (hs : s.Nonempty)
    (hnc : ∀ i ∈ s, ∀ j ∈ s, ℓ i ≠ -ℓ j) :
    (s.filter (fun j => ((s.erase j).image ℓ).card + 1 = s.card ∧
        IsAlt 0 ((s.erase j).image ℓ))).card % 2 = 1 ↔
      ((IsAlt 0 (s.image ℓ) ∨ IsAlt 1 (s.image ℓ)) ∧ (s.image ℓ).card = s.card) := by
  have hNC : NoComp (s.image ℓ) := by
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
    exact hnc i hi j hj
  by_cases hinj : Set.InjOn ℓ s
  · have himg : ∀ j ∈ s, (s.erase j).image ℓ = (s.image ℓ).erase (ℓ j) := by
      intro j hj
      ext x
      simp only [mem_image, mem_erase]
      constructor
      · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
        exact ⟨fun h => hne (hinj ha hj h), a, ha, rfl⟩
      · rintro ⟨hne, a, ha, rfl⟩
        exact ⟨a, ⟨fun h => hne (h ▸ rfl), ha⟩, rfl⟩
    have hcard : (s.image ℓ).card = s.card := card_image_of_injOn hinj
    have hfil : s.filter (fun j => ((s.erase j).image ℓ).card + 1 = s.card ∧
        IsAlt 0 ((s.erase j).image ℓ)) =
        s.filter (fun j => IsAlt 0 ((s.image ℓ).erase (ℓ j))) := by
      apply filter_congr
      intro j hj
      rw [himg j hj, card_erase_of_mem (mem_image_of_mem ℓ hj), hcard]
      have : 1 ≤ s.card := card_pos.2 ⟨j, hj⟩
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by omega, h⟩
    have hcard2 : (s.filter (fun j => IsAlt 0 ((s.image ℓ).erase (ℓ j)))).card =
        ((s.image ℓ).filter (fun a => IsAlt 0 ((s.image ℓ).erase a))).card := by
      rw [filter_image]
      exact (card_image_of_injOn (hinj.mono fun x hx => (mem_filter.1 hx).1)).symm
    rw [hfil, hcard2, count_isAlt_erase _ hNC (hs.image ℓ)]
    simp [hcard]
  · have hcard : (s.image ℓ).card ≠ s.card := fun h => hinj (card_image_iff.1 h)
    simp only [hcard, and_false, iff_false]
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨j1, hj1, j2, hj2, heq, hne⟩ := hinj
    simp only [Finset.mem_coe] at hj1 hj2
    set F := s.filter (fun j => ((s.erase j).image ℓ).card + 1 = s.card ∧
        IsAlt 0 ((s.erase j).image ℓ)) with hF
    have hsub : F ⊆ {j1, j2} := by
      intro j hj
      rw [hF, mem_filter] at hj
      obtain ⟨hjs, hc, -⟩ := hj
      have hinj' : Set.InjOn ℓ (s.erase j) := by
        apply card_image_iff.1
        rw [card_erase_of_mem hjs]
        omega
      by_contra hj12
      simp only [mem_insert, mem_singleton, not_or] at hj12
      exact hne (hinj' (mem_erase.2 ⟨fun h => hj12.1 h.symm, hj1⟩)
        (mem_erase.2 ⟨fun h => hj12.2 h.symm, hj2⟩) heq)
    have he1 : (s.erase j1).image ℓ = s.image ℓ := image_erase_eq_of_dup hj2 (Ne.symm hne) heq.symm
    have he2 : (s.erase j2).image ℓ = s.image ℓ := image_erase_eq_of_dup hj1 hne heq
    have hiff : j1 ∈ F ↔ j2 ∈ F := by
      rw [hF, mem_filter, mem_filter, he1, he2]
      simp [hj1, hj2]
    by_cases h1 : j1 ∈ F
    · have : F = {j1, j2} := by
        apply Subset.antisymm hsub
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h1
        · exact hiff.1 h1
      rw [this, card_pair hne]
      omega
    · have : F = ∅ := by
        apply eq_empty_of_forall_notMem
        intro x hx
        have := hsub hx
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl
        · exact h1 hx
        · exact h1 (hiff.2 hx)
      rw [this, card_empty]
      omega
end KneserColouring
