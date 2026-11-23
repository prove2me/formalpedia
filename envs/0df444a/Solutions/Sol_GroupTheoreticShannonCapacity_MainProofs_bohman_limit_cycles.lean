-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.bohman_limit_cycles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:01.020805+00:00
-- url     : https://prove2.me/submissions/6b7d22e9-3b86-4eda-bd78-6ea6ddb48a8b

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_fractionGraph_two
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_iso


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution :
    ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N,
      |(p : ℝ) / 2 - shannonCapacity (SimpleGraph.cycleGraph p)| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := bohman_limit_fractionGraph_two ε hε
  use max N 2
  intro p hp
  have hp2 : 2 ≤ p := le_of_max_le_right hp
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hp2
  haveI : NeZero p := ⟨ne_of_gt hp_pos⟩
  -- Use the isomorphism: cycleGraph p ≃g fractionGraph p 2
  have hiso := shannonCapacity_iso (cycleGraph_iso_fractionGraph_two p hp2)
  rw [hiso]
  exact hN p (le_of_max_le_left hp)
end GroupTheoreticShannonCapacity.MainProofs
