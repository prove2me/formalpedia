-- Prove2me | solution 1 for NoAdjString.noAdjacentOnes_iff_noAdjacent
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:28:57.683312+00:00
-- url     : https://prove2.me/submissions/a679049d-3bc6-4a98-9d6e-14426e46c40f

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n : ℕ} (f : Fin n → Bool) :
    NoAdjacentOnes f ↔ (supportFinset f).noAdjacent := by
  simp only [NoAdjacentOnes, Finset.noAdjacent, supportFinset, mem_filter]
  constructor
  · intro h x ⟨_, hfx⟩ hnext ⟨_, hfnext⟩
    exact h x hnext ⟨hfx, hfnext⟩
  · intro h i hnext ⟨hfi, hfnext⟩
    exact h i ⟨Finset.mem_univ i, hfi⟩ hnext
      ⟨Finset.mem_univ _, hfnext⟩
