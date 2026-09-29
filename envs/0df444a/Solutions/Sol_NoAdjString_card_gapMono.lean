-- Prove2me | solution 1 for NoAdjString.card_gapMono
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:29:11.122983+00:00
-- url     : https://prove2.me/submissions/bce1f71b-346d-4c97-b387-0d51ee5ad580

import Definitions.Def_NoAdjacentGapEquiv

open Finset Function NoAdjString

theorem solution (n k : ℕ) :
    Fintype.card (GapMono n k) = Nat.choose (n + 1 - k) k := by
  let m := n + 1 - k
  have e1 := gapMonoEquiv n k
  have e2 := strictMonoCardEquiv m k
  rw [Fintype.card_congr e1, Fintype.card_congr e2]
  let pc : Finset (Finset (Fin m)) := Finset.powersetCard k Finset.univ
  have h3 : Fintype.card {s : Finset (Fin m) // s.card = k} = pc.card := by
    rw [Fintype.card_subtype (fun s : Finset (Fin m) => s.card = k)]
    have h4 : Finset.univ.filter (fun s : Finset (Fin m) => s.card = k) = pc := by
      ext s; simp [pc, Finset.mem_powersetCard]
    rw [h4]
  rw [h3, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
