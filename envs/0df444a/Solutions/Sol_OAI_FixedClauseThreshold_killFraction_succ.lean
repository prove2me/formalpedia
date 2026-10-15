-- Prove2me | solution 1 for OAI.FixedClauseThreshold.killFraction_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:18:15.28618+00:00
-- url     : https://prove2.me/submissions/c4bdd820-0a09-40fe-b004-f330c430d523

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Replacement.lean:L27-L46
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.killFraction_succ. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem killFraction_succ {b n r : ℕ} (hrn : r + 1 ≤ n) :
    killFraction b n (r + 1) =
      killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hnc : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : r ≤ n))
  have hncs : (n.choose (r + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hrn)
  have hnr : ((n - r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - r ≠ 0)
  have hb : (b.choose (r + 1) : ℝ) * (r + 1) =
      (b.choose r : ℝ) * ((b - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq b r
  have hn : (n.choose (r + 1) : ℝ) * (r + 1) =
      (n.choose r : ℝ) * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  unfold killFraction
  rw [pow_succ]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a * (n.choose (r + 1) : ℝ)) hb,
    congrArg (fun a : ℝ => a * (b.choose (r + 1) : ℝ)) hn]

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.killFraction_succ := @_root_.OAI.FixedClauseThreshold.killFraction_succ
