-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.summable_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:21.07891+00:00
-- url     : https://prove2.me/submissions/5090d4ce-b511-4085-88cf-d3b6bb403261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_bound
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_zero_row

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
theorem _root_.solution (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) (m : ℤ) :
    Summable fun n : ℤ => (((m : ℝ) * x + n) ^ 2 + (m * y) ^ 2) ^ (-s) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using summable_zero_row hs
  · have := (rowSum_bound (m * x) (Y := |m * y|) (by positivity) hs).1
    simpa only [sq_abs] using this
end GlobalTheory.KroneckerLimit
