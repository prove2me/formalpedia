-- Prove2me | solution 1 for InteractiveConsistency.Impossibility.partition_of_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:04:18.376987+00:00
-- url     : https://prove2.me/submissions/53017058-5384-4109-ba58-1e277fef20da

import Mathlib



namespace InteractiveConsistency.Impossibility

lemma partition_core {α : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∃ A B C : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = P ∧
      A.card ≤ m ∧ B.card ≤ m ∧ C.card ≤ m := by
  obtain ⟨A, hAP, hA⟩ := Finset.exists_subset_card_eq (s := P) (n := min m (P.card - 2)) (by omega)
  have hcard : (P \ A).card = P.card - A.card := Finset.card_sdiff_of_subset hAP
  obtain ⟨B, hBP, hB⟩ := Finset.exists_subset_card_eq (s := P \ A)
    (n := min m (P.card - A.card - 1)) (by omega)
  have hBc : ((P \ A) \ B).card = (P \ A).card - B.card := Finset.card_sdiff_of_subset hBP
  refine ⟨A, B, (P \ A) \ B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]; omega
  · rw [← Finset.card_pos]; omega
  · rw [← Finset.card_pos]; omega
  · exact Finset.disjoint_left.2 fun x hxA hxB => (Finset.mem_sdiff.1 (hBP hxB)).2 hxA
  · exact Finset.disjoint_left.2 fun x hxA hxC =>
      (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hxC).1).2 hxA
  · exact Finset.disjoint_left.2 fun x hxB hxC => (Finset.mem_sdiff.1 hxC).2 hxB
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | h)
      · exact hAP h
      · exact (Finset.mem_sdiff.1 (hBP h)).1
      · exact h.1.1
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr hxB)
        · exact Or.inr ⟨⟨hx, hxA⟩, hxB⟩
  · omega
  · omega
  · omega

end InteractiveConsistency.Impossibility

open InteractiveConsistency.Impossibility


theorem solution {α : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∃ A B C : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = P ∧
      A.card ≤ m ∧ B.card ≤ m ∧ C.card ≤ m := by
  exact partition_core P m h3 hn
