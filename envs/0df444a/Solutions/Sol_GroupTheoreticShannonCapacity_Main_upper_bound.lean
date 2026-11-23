-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:08.964617+00:00
-- url     : https://prove2.me/submissions/6ab14568-b3bc-43a4-95b3-111cb735b2a1

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_le


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (p q : ℕ) [NeZero p] (hq : 0 < q) (hpq : q ≤ p) :
    shannonCapacity (fractionGraph p q) ≤ p / q :=
  shannonCapacity_fractionGraph_le p q hq hpq
end GroupTheoreticShannonCapacity.Main
