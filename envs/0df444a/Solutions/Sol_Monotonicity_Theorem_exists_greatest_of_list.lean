-- Prove2me | solution 1 for Monotonicity_Theorem.exists_greatest_of_list
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:43:22.598257+00:00
-- url     : https://prove2.me/submissions/fef0aa9c-7c90-46ec-9662-8244b3183954

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (hNe : L ≠ []) :
    ∃ M : R, M ∈ L ∧ ∀ r : R, r ∈ L → (D.lt r M ∨ r = M) := by
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
      obtain ⟨MB, hMBin, hMBupper⟩ := ih hBne
      by_cases hlt : D.lt MB x
      · refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
        cases hr with
        | head => exact Or.inr rfl
        | tail _ hrB =>
          cases hMBupper r hrB with
          | inl h => exact Or.inl (D.trans h hlt)
          | inr heq => exact Or.inl (by rw [heq]; exact hlt)
      · refine ⟨MB, List.Mem.tail _ hMBin, fun r hr => ?_⟩
        cases hr with
        | head =>
          rcases D.trichotomy MB x with ⟨h, _, _⟩ | ⟨heq, _, _⟩ | ⟨h, _, _⟩
          · exact absurd h hlt
          · exact Or.inr heq.symm
          · exact Or.inl h
        | tail _ hrB => exact hMBupper r hrB
