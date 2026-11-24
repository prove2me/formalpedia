-- Prove2me | solution 1 for GlobalTheory.SummableExpNegAbsSum.summable_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:44.499024+00:00
-- url     : https://prove2.me/submissions/3d4fba6f-0e43-4819-937d-e3e8ac10186b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableExpNegAbsSum
namespace GlobalTheory.SummableExpNegAbsSum
theorem _root_.solution : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by
  have h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ)) := Real.summable_exp_neg_nat
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h
end GlobalTheory.SummableExpNegAbsSum
