-- Prove2me | solution 1 for N25.level25_subgroup_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:49.386695+00:00
-- url     : https://prove2.me/submissions/c232acbe-30dc-453e-a344-03439a224d6f

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_card

set_option autoImplicit false

namespace N25

/-- The diamond label group has five cosets modulo the level subgroup. -/
theorem _root_.solution : H25.index = 5 := by
  have hall : Nat.card (ZMod 25)ˣ = 20 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h := H25.card_mul_index
  rw [level25_subgroup_card, hall] at h
  omega

end N25
