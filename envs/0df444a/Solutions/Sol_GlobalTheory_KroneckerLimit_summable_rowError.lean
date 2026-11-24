-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.summable_rowError
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:21.67385+00:00
-- url     : https://prove2.me/submissions/ce27512c-13c8-4bf8-b0ee-3ce190aaf05d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_bound
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_sq_rpow

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
theorem _root_.solution (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m => rowError x y m s :=
  .of_norm_bounded (summable_sq_rpow hy hs) fun m =>
    (rowSum_bound _ (by positivity) hs).2
end GlobalTheory.KroneckerLimit
