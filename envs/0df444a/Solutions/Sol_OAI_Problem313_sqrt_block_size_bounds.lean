-- Prove2me | solution 1 for OAI.Problem313.sqrt_block_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:54:17.794978+00:00
-- url     : https://prove2.me/submissions/e1b73d26-5e81-41bc-9193-e29e7f41c7dd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockSize.lean:L14-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.sqrt_block_size_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit

-- ---- from OAI.Combinatorics.SharpThreshold.BlockSize ----
namespace OAI

noncomputable section

namespace Problem313

theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.sub_one_lt_floor x
  linarith

/-- Elementary size estimates for the square-root vertex block. -/
theorem sqrt_block_size_bounds (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    3 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ ∧
      ⌊Real.sqrt (n : ℝ)⌋₊ ≤ n ∧
      Real.sqrt (n : ℝ) / 2 ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlarge : 17 ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hsqrt : 4 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  refine ⟨Nat.le_floor (by norm_num; linarith), ?_, half_le_nat_floor (by linarith)⟩
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.sqrt_block_size_bounds := @_root_.OAI.Problem313.sqrt_block_size_bounds
