-- Prove2me | solution 1 for NoAdjString.mem_noAdjacentStringsCard
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:29:06.831827+00:00
-- url     : https://prove2.me/submissions/bfb41dd5-f5ac-46ba-9be4-81d008a1c23e

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n k : ℕ} {f : Fin n → Bool} :
    f ∈ noAdjacentStringsCard n k ↔
      NoAdjacentOnes f ∧ (supportFinset f).card = k := by
  simp [noAdjacentStringsCard, noAdjacentStrings]
