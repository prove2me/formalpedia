-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.limit_fraction_graphs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:07:44.248804+00:00
-- url     : https://prove2.me/submissions/63832770-1b59-48f1-b42f-482cb48d0a93

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_fraction_graphs


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (ε : ℝ) (hε : ε > 0) :
    ∃ M : ℝ, ∀ p q : ℕ, [NeZero p] → (q : ℝ) > 0 → (p : ℝ) / q > M →
      |(p : ℝ) / q - shannonCapacity (fractionGraph p q)| < ε :=
  bohman_limit_fraction_graphs ε hε
end GroupTheoreticShannonCapacity.Main
