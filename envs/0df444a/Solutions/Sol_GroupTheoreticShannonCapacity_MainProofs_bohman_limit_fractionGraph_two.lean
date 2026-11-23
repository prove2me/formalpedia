-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.bohman_limit_fractionGraph_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:07:43.84964+00:00
-- url     : https://prove2.me/submissions/491ca78c-3cce-4871-911d-1697033dee55

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_fraction_graphs

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution :
    ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, [NeZero p] →
      |(p : ℝ) / 2 - shannonCapacity (fractionGraph p 2)| < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := bohman_limit_fraction_graphs ε hε
  -- Choose N so that p ≥ N implies p/2 > M
  use max (Nat.ceil (2 * M) + 1) 2
  intro p hp _
  have hp_ge_2 : 2 ≤ p := le_of_max_le_right hp
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp_ge_2
  apply hM p 2 (by norm_num : (2 : ℝ) > 0)
  -- Show p/2 > M
  have h1 : (p : ℝ) ≥ Nat.ceil (2 * M) + 1 := by
    have h2 : p ≥ Nat.ceil (2 * M) + 1 := le_of_max_le_left hp
    exact_mod_cast h2
  have h2 : (Nat.ceil (2 * M) : ℝ) ≥ 2 * M := Nat.le_ceil (2 * M)
  calc (p : ℝ) / 2 ≥ (Nat.ceil (2 * M) + 1) / 2 := by
        apply div_le_div_of_nonneg_right h1; norm_num
    _ > (2 * M) / 2 := by linarith
    _ = M := by ring
end GroupTheoreticShannonCapacity.MainProofs
