-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.limit_cycles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:11:36.103258+00:00
-- url     : https://prove2.me/submissions/7c0fe5fe-323c-4afd-9c0f-225da3984884

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_cycles


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ p ≥ N,
      |p / 2 - shannonCapacity (SimpleGraph.cycleGraph p)| < ε :=
  bohman_limit_cycles ε hε
end GroupTheoreticShannonCapacity.Main
