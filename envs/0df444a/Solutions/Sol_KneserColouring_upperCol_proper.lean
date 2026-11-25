-- Prove2me | solution 1 for KneserColouring.upperCol_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:05.43889+00:00
-- url     : https://prove2.me/submissions/6042b58e-ee30-4707-af0e-83dae1a61fd2

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (hk : 0 < k) (hn : 2 * k ≤ n) (s t : {s : Finset (Fin n) // s.card = k})
    (hd : Disjoint s.1 t.1) : upperCol hk s ≠ upperCol hk t := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [upperCol] at hv
  set a := s.1.min' (card_pos.1 (by rw [s.2]; exact hk)) with ha
  set b := t.1.min' (card_pos.1 (by rw [t.2]; exact hk)) with hb
  have has : a ∈ s.1 := min'_mem _ _
  have hbt : b ∈ t.1 := min'_mem _ _
  by_cases hlt : a.val < n - 2 * k + 1 ∨ b.val < n - 2 * k + 1
  · have hab : a = b := Fin.ext (by omega)
    rw [hab] at has
    exact disjoint_left.1 hd has hbt
  · rw [not_or, not_lt, not_lt] at hlt
    have hsub : s.1 ∪ t.1 ⊆ univ.filter (fun i : Fin n => n - 2 * k + 1 ≤ i.val) := by
      intro i hi
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rcases mem_union.1 hi with hi | hi
      · have := min'_le s.1 i hi
        have : a.val ≤ i.val := this
        omega
      · have := min'_le t.1 i hi
        have : b.val ≤ i.val := this
        omega
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hd, s.2, t.2] at h1
    have h2 : (univ.filter (fun i : Fin n => n - 2 * k + 1 ≤ i.val)).card ≤
        (Ico (n - 2 * k + 1) n).card := by
      apply card_le_card_of_injOn (fun i => i.val)
      · intro i hi
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
        simp only [coe_Ico, Set.mem_Ico]
        exact ⟨hi, i.isLt⟩
      · intro i _ j _ h
        exact Fin.ext h
    rw [Nat.card_Ico] at h2
    omega
end KneserColouring
