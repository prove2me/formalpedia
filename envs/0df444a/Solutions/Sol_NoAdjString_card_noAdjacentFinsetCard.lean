-- Prove2me | solution 1 for NoAdjString.card_noAdjacentFinsetCard
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:30:08.067982+00:00
-- url     : https://prove2.me/submissions/b916d626-2332-4ba9-9d96-53f58eb0c867

import Theorems.Thm_NoAdjString_card_gapMono
import Definitions.Def_NoAdjacentGapEquiv

open Finset Function NoAdjString

theorem solution (n k : ℕ) :
    (noAdjacentFinsetCard n k).card = Nat.choose (n + 1 - k) k := by
  have h1 : Fintype.card {s : Finset (Fin n) // s ∈ noAdjacentFinsetCard n k} =
      (noAdjacentFinsetCard n k).card := by
    rw [Fintype.card_subtype (fun s : Finset (Fin n) => s ∈ noAdjacentFinsetCard n k)]
    have h2 : Finset.univ.filter (fun s : Finset (Fin n) => s ∈ noAdjacentFinsetCard n k) =
        noAdjacentFinsetCard n k := by
      ext s; simp
    rw [h2]
  have h3 : Fintype.card {s : Finset (Fin n) // s ∈ noAdjacentFinsetCard n k} =
      Fintype.card (GapMono n k) := Fintype.card_congr (noAdjacentFinsetCardEquiv n k)
  rw [←h1, h3, card_gapMono]
