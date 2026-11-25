-- Prove2me | solution 1 for HiltonMilner.exists_hiltonMilner_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:02.727511+00:00
-- url     : https://prove2.me/submissions/8d3cc43a-3475-4f08-a68a-918e9af6f52d

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Theorems.Thm_HiltonMilner_card_meeting_gen

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) :
    ∃ 𝒜 : Finset (Finset (Fin n)), (𝒜 : Set (Finset (Fin n))).Intersecting ∧
      (𝒜 : Set (Finset (Fin n))).Sized k ∧ (∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) ∧
      #𝒜 = (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by
  have hn0 : 0 < n := by omega
  set o : Fin n := ⟨0, hn0⟩
  set B : Finset (Fin n) := univ.filter (fun x : Fin n => 1 ≤ x.val ∧ x.val ≤ k)
  have hmemB : ∀ x : Fin n, x ∈ B ↔ 1 ≤ x.val ∧ x.val ≤ k := by
    intro x; simp only [B, mem_filter, mem_univ, true_and]
  have hBcard : #B = k := by
    have : B.map Fin.valEmbedding = Icc 1 k := by
      ext x
      simp only [mem_map, mem_Icc, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact (hmemB y).1 hy
      · rintro ⟨h1, h2⟩; exact ⟨⟨x, by omega⟩, (hmemB _).2 ⟨h1, h2⟩, rfl⟩
    rw [← card_map Fin.valEmbedding, this, Nat.card_Icc]; omega
  have hoB : o ∉ B := by rw [hmemB]; simp [o]
  set 𝒮 := (powersetCard k (univ : Finset (Fin n))).filter (fun A => o ∈ A ∧ (A ∩ B).Nonempty)
  refine ⟨insert B 𝒮, ?_, ?_, ?_, ?_⟩
  · -- intersecting
    intro A hA C hC
    rw [mem_coe, mem_insert] at hA hC
    rw [not_disjoint_iff_nonempty_inter]
    rcases hA with rfl | hA <;> rcases hC with rfl | hC
    · rw [inter_self, ← card_pos, hBcard]; omega
    · rw [inter_comm]; exact (mem_filter.1 hC).2.2
    · exact (mem_filter.1 hA).2.2
    · exact ⟨o, mem_inter.2 ⟨(mem_filter.1 hA).2.1, (mem_filter.1 hC).2.1⟩⟩
  · -- uniform
    intro A hA
    rw [mem_coe, mem_insert] at hA
    rcases hA with rfl | hA
    · exact hBcard
    · exact (mem_powersetCard.1 (mem_filter.1 hA).1).2
  · -- nontrivial
    intro x
    by_cases hxB : x ∈ B
    · have hxo : x ≠ o := fun h => hoB (h ▸ hxB)
      refine ⟨insert o (B.erase x), mem_insert_of_mem (mem_filter.2 ⟨?_, mem_insert_self _ _, ?_⟩),
        ?_⟩
      · refine mem_powersetCard.2 ⟨subset_univ _, ?_⟩
        rw [card_insert_of_notMem (fun h => hoB (mem_of_mem_erase h)), card_erase_of_mem hxB,
          hBcard]
        omega
      · have : 0 < #(B.erase x) := by rw [card_erase_of_mem hxB, hBcard]; omega
        obtain ⟨w, hw⟩ := card_pos.1 this
        exact ⟨w, mem_inter.2 ⟨mem_insert_of_mem hw, mem_of_mem_erase hw⟩⟩
      · rw [mem_insert, mem_erase]
        rintro (h | ⟨h, -⟩)
        · exact hxo h
        · exact h rfl
    · exact ⟨B, mem_insert_self _ _, hxB⟩
  · -- size
    have hBnot : B ∉ 𝒮 := fun h => hoB (mem_filter.1 h).2.1
    rw [card_insert_of_notMem hBnot]
    set Y := (univ : Finset (Fin n)).erase o
    have hY : #Y = n - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have hBY : B ⊆ Y := fun w hw => mem_erase.2 ⟨fun h => hoB (h ▸ hw), mem_univ _⟩
    have h𝒮 : 𝒮 = ((powersetCard (k - 1) Y).filter (fun D => (D ∩ B).Nonempty)).image
        (insert o) := by
      ext A
      simp only [𝒮, mem_filter, mem_powersetCard, mem_image, subset_univ, true_and]
      constructor
      · rintro ⟨hA, hoA, hAB⟩
        refine ⟨A.erase o, ⟨⟨fun w hw => mem_erase.2 ⟨ne_of_mem_erase hw, mem_univ _⟩, ?_⟩, ?_⟩,
          insert_erase hoA⟩
        · rw [card_erase_of_mem hoA, hA]
        · obtain ⟨w, hw⟩ := hAB
          rw [mem_inter] at hw
          exact ⟨w, mem_inter.2 ⟨mem_erase.2 ⟨fun h => hoB (h ▸ hw.2), hw.1⟩, hw.2⟩⟩
      · rintro ⟨D, ⟨⟨hDY, hD⟩, hDB⟩, rfl⟩
        have hoD : o ∉ D := fun h => (mem_erase.1 (hDY h)).1 rfl
        refine ⟨?_, mem_insert_self _ _, ?_⟩
        · rw [card_insert_of_notMem hoD, hD]; omega
        · obtain ⟨w, hw⟩ := hDB
          exact ⟨w, mem_inter.2 ⟨mem_insert_of_mem (mem_inter.1 hw).1, (mem_inter.1 hw).2⟩⟩
    have hinj : Set.InjOn (insert o)
        (((powersetCard (k - 1) Y).filter (fun D => (D ∩ B).Nonempty) : Finset (Finset (Fin n))) :
          Set (Finset (Fin n))) := by
      intro D hD D' hD' h
      simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at hD hD'
      have hoD : o ∉ D := fun h => (mem_erase.1 (hD.1.1 h)).1 rfl
      have hoD' : o ∉ D' := fun h => (mem_erase.1 (hD'.1.1 h)).1 rfl
      rw [← erase_insert hoD, ← erase_insert hoD']
      exact congrArg (fun S => S.erase o) h
    rw [h𝒮, card_image_of_injOn hinj, card_meeting_gen hBY, hY, hBcard,
      show n - 1 - k = n - k - 1 by omega]
end HiltonMilner
