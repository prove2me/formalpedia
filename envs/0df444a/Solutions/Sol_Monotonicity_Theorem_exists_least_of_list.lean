-- Prove2me | solution 1 for Monotonicity_Theorem.exists_least_of_list
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:41.594105+00:00
-- url     : https://prove2.me/submissions/42c010ca-47c0-4fa7-84ee-2284385ec9cf

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (hNe : L ≠ []) :
    ∃ m : R, m ∈ L ∧ ∀ r : R, r ∈ L → (D.lt m r ∨ m = r) := by
  induction L with
  | nil => contradiction
  | cons x B ih =>
    by_cases hB : B = []
    · subst hB
      refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
      cases hr with
      | head => exact Or.inr rfl
      | tail _ h => cases h
    · have hBne : B ≠ [] := hB
      obtain ⟨mB, hmBin, hmBlower⟩ := ih hBne
      by_cases hlt : D.lt x mB
      · refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
        cases hr with
        | head => exact Or.inr rfl
        | tail _ hrB =>
          cases hmBlower r hrB with
          | inl h => exact Or.inl (D.trans hlt h)
          | inr heq => exact Or.inl (by rw [← heq]; exact hlt)
      · refine ⟨mB, List.Mem.tail _ hmBin, fun r hr => ?_⟩
        cases hr with
        | head =>
          rcases D.trichotomy x mB with ⟨h, _, _⟩ | ⟨heq, _, _⟩ | ⟨h, _, _⟩
          · exact absurd h hlt
          · exact Or.inr heq.symm
          · exact Or.inl h
        | tail _ hrB => exact hmBlower r hrB
