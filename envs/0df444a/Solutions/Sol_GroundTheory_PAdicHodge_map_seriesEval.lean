-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_seriesEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:14.851037+00:00
-- url     : https://prove2.me/submissions/cbde8b1b-d45f-4b03-b4f2-6308f6d68a97

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_eq_of_forall_sub_mem_pow
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_sub_sum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_map_partialSum

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
theorem _root_.solution {B' : Type*} [CommRing B'] [Algebra ℚ B'] {I' : Ideal B'}
    [IsAdicComplete I' B'] (F : B →+* B') (hF : I.map F ≤ I') {z : B} (hz : z ∈ I)
    (hFz : F z ∈ I') (f : ℚ⟦X⟧) : F (seriesEval I z hz f) = seriesEval I' (F z) hFz f := by
  refine eq_of_forall_sub_mem_pow I' fun n => ?_
  have h1 : F (seriesEval I z hz f - ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) ∈
      I' ^ n := by
    have := Ideal.mem_map_of_mem F (seriesEval_sub_sum_mem hz f n)
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hF n this
  have h2 := seriesEval_sub_sum_mem hFz f n
  rw [map_sub, map_partialSum] at h1
  have := sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right] at this
end GroundTheory.PAdicHodge
