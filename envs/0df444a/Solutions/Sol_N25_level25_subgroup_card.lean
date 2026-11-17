-- Prove2me | solution 1 for N25.level25_subgroup_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:45.794737+00:00
-- url     : https://prove2.me/submissions/68cce5f7-f6b9-4ba3-b7dd-e4be693cafe8

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_membership

set_option autoImplicit false

namespace N25

/-- The existing level subgroup has four elements. -/
theorem _root_.solution : Nat.card H25 = 4 := by
  let e : H25 ≃ {u : (ZMod 25)ˣ //
      (u : ZMod 25) = 1 ∨ (u : ZMod 25) = 7 ∨
      (u : ZMod 25) = 18 ∨ (u : ZMod 25) = 24} :=
    Equiv.subtypeEquivRight level25_subgroup_membership
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

end N25
