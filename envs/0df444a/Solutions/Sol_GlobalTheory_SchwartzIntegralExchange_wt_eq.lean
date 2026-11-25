-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:28.398841+00:00
-- url     : https://prove2.me/submissions/79142919-b437-47aa-b63e-bdcefad40f4a

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
theorem _root_.solution (k n : ℕ) (w : SchwartzMap E ℂ) : wt k n w = wtFun k n w := rfl
end GlobalTheory.SchwartzIntegralExchange
