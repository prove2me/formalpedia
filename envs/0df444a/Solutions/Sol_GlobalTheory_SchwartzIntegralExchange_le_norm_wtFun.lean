-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.le_norm_wtFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:45.046552+00:00
-- url     : https://prove2.me/submissions/1838d17c-d10b-40ef-bb91-4140cc7c021f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.SchwartzIntegralExchange
theorem _root_.solution (k n : ℕ) (w : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k n w ≤ ‖wtFun k n w‖ := by
  refine SchwartzMap.seminorm_le_bound ℂ k n w (norm_nonneg _) (fun x => ?_)
  have := (wtFun k n w).norm_coe_le_norm x
  rwa [wtFun_apply, norm_smul, Real.norm_of_nonneg (by positivity)] at this
end GlobalTheory.SchwartzIntegralExchange
