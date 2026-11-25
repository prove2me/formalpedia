-- Prove2me | solution 1 for GroundTheory.PAdicHodge.logOnePlus_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:54.959955+00:00
-- url     : https://prove2.me/submissions/4c656e79-666f-45ba-afbe-bea03be9eb26

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_sub_sum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.seriesEval_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) (n : ℕ) :
    logOnePlus I z hz - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ B ((-1) ^ (i + 1) / i) * z ^ i ∈
      I ^ n := by
  have hs : ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ B ((-1) ^ (i + 1) / i) * z ^ i =
      ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i (log ℚ)) * z ^ i := by
    rcases n with _ | n
    · simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), coeff_log,
        if_pos rfl, map_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [coeff_log, if_neg (by have := (Finset.mem_Ico.1 hi).1; omega), Algebra.algebraMap_self,
        RingHom.id_apply]
  rw [hs]
  exact seriesEval_sub_sum_mem hz (log ℚ) n
end GroundTheory.PAdicHodge
