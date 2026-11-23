-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Main.subgroup_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:38.137822+00:00
-- url     : https://prove2.me/submissions/26f6dd6c-c1ac-4a8f-a1ae-c9cd20be30a5

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_subgroup_capacity_limit


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
namespace GroupTheoreticShannonCapacity.Main
theorem _root_.solution (ε : ℝ) (hε : ε > 0) :
    ∃ M : ℝ, ∀ p q : ℕ, p ≠ 0 → 0 < q → (p : ℝ) / q > M →
      ∃ (a b : ℕ) (_ : NeZero a), (a : ℚ) / b = (p : ℚ) / q ∧
        (p : ℝ) / q - addSubgroupShannonCapacity (fractionGraph a b) < ε :=
  subgroup_capacity_limit ε hε
end GroupTheoreticShannonCapacity.Main
