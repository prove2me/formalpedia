-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.wt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.684239+00:00
-- url     : https://prove2.me/submissions/f798e168-ee11-43d3-8f96-a0c1cbda50ea

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
theorem _root_.solution (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wt k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl
end GlobalTheory.SchwartzIntegralExchange
