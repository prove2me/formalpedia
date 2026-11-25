-- Prove2me | solution 1 for GroundTheory.PAdicHodge.seriesEval_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:31.023586+00:00
-- url     : https://prove2.me/submissions/ada129c6-edae-41b9-a131-574b5de87d36

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_mk_seriesEval

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
theorem _root_.solution {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    seriesEval I z hz f - ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i ∈ I ^ n :=
  Ideal.Quotient.eq.1 (mk_seriesEval hz f n)
end GroundTheory.PAdicHodge
