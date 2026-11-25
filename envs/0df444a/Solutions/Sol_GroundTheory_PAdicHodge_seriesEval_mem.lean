-- Prove2me | solution 1 for GroundTheory.PAdicHodge.seriesEval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:36:28.403678+00:00
-- url     : https://prove2.me/submissions/0a18fcbc-4849-4f9f-b519-4db8433f45a4

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
theorem _root_.solution {z : B} (hz : z ∈ I) {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    seriesEval I z hz f ∈ I := by
  have h := seriesEval_sub_sum_mem hz f 1
  rwa [Finset.sum_range_one, coeff_zero_eq_constantCoeff_apply, hf, map_zero, zero_mul, sub_zero,
    pow_one] at h
end GroundTheory.PAdicHodge
