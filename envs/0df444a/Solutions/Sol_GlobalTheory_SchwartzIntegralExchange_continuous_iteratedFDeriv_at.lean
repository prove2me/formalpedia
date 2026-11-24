-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.continuous_iteratedFDeriv_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:58.185705+00:00
-- url     : https://prove2.me/submissions/f4b286e8-a5d9-45bc-a45b-38ef3b9fb9b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_wt_apply

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
theorem _root_.solution (n : ℕ) (x : E) :
    Continuous (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) := by
  have : (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) = fun w => wt 0 n w x := by
    funext w; simp [wt_apply]
  rw [this]
  exact (continuous_eval_const x).comp (wt 0 n).continuous
end GlobalTheory.SchwartzIntegralExchange
