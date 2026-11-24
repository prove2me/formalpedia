-- Prove2me | solution 1 for GlobalTheory.hsGrowth_log_add_div_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:00:11.833265+00:00
-- url     : https://prove2.me/submissions/d50c62d4-40d4-45e3-8076-dfc699cac684

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii

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
theorem _root_.solution (D : ℕ) :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ) + D) / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(D : ℝ)) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ (D : ℝ) tendsto_natCast_atTop_atTop)
  refine h.congr (fun m => ?_)
  simp
end GlobalTheory
