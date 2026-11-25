-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tendsto_seriesEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:01.191637+00:00
-- url     : https://prove2.me/submissions/2abe8c9f-a726-4e33-93dc-352eb274cc26

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
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
theorem _root_.solution {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) :
    @Filter.Tendsto ℕ B (fun n => ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i)
      Filter.atTop (@nhds B I.adicTopology (seriesEval I z hz f)) := by
  let _ := I.adicTopology
  rw [(Ideal.hasBasis_nhds_adic I (seriesEval I z hz f)).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  refine ⟨_, Ideal.pow_le_pow_right hN (neg_mem (seriesEval_sub_sum_mem hz f N)), ?_⟩
  simp
end GroundTheory.PAdicHodge
