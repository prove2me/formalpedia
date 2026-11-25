-- Prove2me | solution 1 for GroundTheory.PAdicHodge.seriesEval_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:36:28.338319+00:00
-- url     : https://prove2.me/submissions/bd001cc4-aa21-482b-bcae-40ef470a638f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_eq_of_forall_sub_mem_pow
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_sub_sum_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) : seriesEval I z hz X = z := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  refine Ideal.pow_le_pow_right (Nat.le_add_right n 2) ?_
  have h := seriesEval_sub_sum_mem hz X (n + 2)
  rwa [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, coeff_zero_X,
    coeff_one_X, map_zero, map_one, zero_mul, add_zero, pow_one, one_mul, zero_add] at h
  intro i _
  rw [coeff_X, if_neg (by omega), map_zero, zero_mul]
end GroundTheory.PAdicHodge
