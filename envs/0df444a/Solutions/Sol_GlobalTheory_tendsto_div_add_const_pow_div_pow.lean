-- Prove2me | solution 1 for GlobalTheory.tendsto_div_add_const_pow_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:50.079751+00:00
-- url     : https://prove2.me/submissions/5b7d23a4-1b49-47c8-9573-1e132027d535

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBounds

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
theorem _root_.solution (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp
end GlobalTheory
