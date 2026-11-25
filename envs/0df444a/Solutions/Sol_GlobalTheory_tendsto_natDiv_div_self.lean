-- Prove2me | solution 1 for GlobalTheory.tendsto_natDiv_div_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:23:59.390865+00:00
-- url     : https://prove2.me/submissions/ab935ede-e502-4254-b4e8-819463a652a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyLeAtNearbyIndices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((M:ℝ) / n)
      rw [Nat.floor_div_eq_div] at this
      linarith
    rw [le_div_iff₀ hMR]
    have : (1 / (n:ℝ) - 1 / M) * M = M / n - 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMR]
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := n)
    have e : 1 / (n:ℝ) * M = M / n := by ring
    linarith
end GlobalTheory
