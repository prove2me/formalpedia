-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.Numerical.log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:15:08.373787+00:00
-- url     : https://prove2.me/submissions/1da2c46c-114d-44ed-8d2f-c8319ea0e28c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Numerical.lean:L18-L32
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.Numerical.log_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

lemma log_bounds {x : ℝ} (hx : 32 ≤ x) : 1 ≤ Real.log x ∧ 7 * Real.log x ≤ x := by
  have hx0 : 0 < x := by linarith
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ x by linarith)
  rw [h4] at hlower
  have hupper := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 32))
  rw [Real.log_div hx0.ne' (by norm_num), h32] at hupper
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  constructor <;> linarith

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.Numerical.log_bounds := @_root_.OAI.CliqueFreeIndependence.Numerical.log_bounds
