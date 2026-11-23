-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:19.611736+00:00
-- url     : https://prove2.me/submissions/89e2d945-1bb0-4073-8c5e-7ac8c4df3fbe

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_mono


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    shannonCapacity (fractionGraph a b) ≤ shannonCapacity (fractionGraph c d) :=
  shannonCapacity_fractionGraph_mono a b c d hb_pos hab_le_cd
end GroupTheoreticShannonCapacity.Main
