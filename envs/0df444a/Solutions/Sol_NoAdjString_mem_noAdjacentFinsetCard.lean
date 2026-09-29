-- Prove2me | solution 1 for NoAdjString.mem_noAdjacentFinsetCard
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:29:08.510121+00:00
-- url     : https://prove2.me/submissions/bb994d55-4af8-43d7-be34-e1199881ca5a

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ noAdjacentFinsetCard n k ↔ s.noAdjacent ∧ s.card = k := by
  simp [noAdjacentFinsetCard, noAdjacentFinset]
