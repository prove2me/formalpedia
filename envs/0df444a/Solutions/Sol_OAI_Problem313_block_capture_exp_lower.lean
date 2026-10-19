-- Prove2me | solution 1 for OAI.Problem313.block_capture_exp_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:55:48.358987+00:00
-- url     : https://prove2.me/submissions/bd8db1be-ed66-4b1d-a419-f0bac4d7119b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockSize.lean:L63-L84
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.block_capture_exp_lower. The node keeps its source
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

/-- A coarse exponential estimate sufficient for the block-capture union bound. -/
theorem block_capture_exp_lower (t : ℝ) (ht : 16 ≤ t) :
    2 * t ^ 2 ≤ Real.exp (t / 2) := by
  have htpos : 0 ≤ t := by linarith
  have hsq : 16 * t ≤ t ^ 2 := by
    nlinarith [mul_nonneg htpos (sub_nonneg.mpr ht)]
  have hcube : 256 * t ≤ t ^ 3 := by
    calc
      256 * t ≤ 16 * t ^ 2 := by linarith
      _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
      _ = t ^ 3 := by ring
  have hexp := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ t / 4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have hlower : (17 / 12 : ℝ) * t ≤ Real.exp (t / 4) := by
    nlinarith
  have hsquare : ((17 / 12 : ℝ) * t) ^ 2 ≤ (Real.exp (t / 4)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlower 2
  have hid : Real.exp (t / 2) = (Real.exp (t / 4)) ^ 2 := by
    rw [show t / 2 = t / 4 + t / 4 by ring, Real.exp_add]
    ring
  rw [hid]
  nlinarith [sq_nonneg t]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.block_capture_exp_lower := @_root_.OAI.Problem313.block_capture_exp_lower
