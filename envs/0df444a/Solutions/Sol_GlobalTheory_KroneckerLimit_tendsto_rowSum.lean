-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tendsto_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:22.367074+00:00
-- url     : https://prove2.me/submissions/408b092b-4741-4550-bebd-674c9266f6ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_bound
import Theorems.Thm_GlobalTheory_KroneckerLimit_rpow_neg_le
import Theorems.Thm_GlobalTheory_KroneckerLimit_eventually_mem_Ioc_one_two
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_rpow_neg

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
theorem _root_.solution (a : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (rowSum a Y) (𝓝[>] 1) (𝓝 (rowSum a Y 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((rowSum_bound a hY le_rfl).1.add (rowSum_bound a hY one_le_two).1)
    (fun n => tendsto_rpow_neg (by positivity)) ?_
  filter_upwards [eventually_mem_Ioc_one_two] with s hs n
  rw [Real.norm_of_nonneg (by positivity)]
  exact rpow_neg_le (by positivity) hs.1.le hs.2
end GlobalTheory.KroneckerLimit
