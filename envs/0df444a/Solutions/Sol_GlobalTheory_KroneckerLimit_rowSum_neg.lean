-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.rowSum_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:46.683025+00:00
-- url     : https://prove2.me/submissions/79d965cd-2641-4d95-9ee1-482536be7335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (a Y s : ℝ) : rowSum (-a) (-Y) s = rowSum a Y s := by
  rw [rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1 with n
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring
end GlobalTheory.KroneckerLimit
