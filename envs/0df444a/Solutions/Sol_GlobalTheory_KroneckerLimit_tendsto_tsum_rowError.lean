-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tendsto_tsum_rowError
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:47.341027+00:00
-- url     : https://prove2.me/submissions/399113d0-6e8e-4aa0-b535-328e3b19e456

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_bound
import Theorems.Thm_GlobalTheory_KroneckerLimit_rpow_neg_le
import Theorems.Thm_GlobalTheory_KroneckerLimit_eventually_mem_Ioc_one_two
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_rowSum
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_sq_rpow
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasDerivAt_betaConst_one


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
theorem _root_.solution (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s => ∑' m, rowError x y m s) (𝓝[>] 1) (𝓝 (∑' m, rowError x y m 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sq_rpow hy le_rfl).add (summable_sq_rpow hy one_le_two)) (fun m => ?_) ?_
  · have hY : 0 < ((m : ℝ) + 1) * y := by positivity
    refine (tendsto_rowSum _ hY).sub (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
    refine hasDerivAt_betaConst_one.continuousAt.tendsto.mul ?_
    exact ((Real.continuousAt_const_rpow hY.ne').comp (f := fun s : ℝ => 1 - 2 * s)
      (by fun_prop)).tendsto
  · filter_upwards [eventually_mem_Ioc_one_two] with s hs m
    exact (rowSum_bound _ (by positivity) hs.1.le).2.trans (rpow_neg_le (by positivity) hs.1.le hs.2)
end GlobalTheory.KroneckerLimit
