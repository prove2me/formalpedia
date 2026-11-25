-- Prove2me | solution 1 for GroundTheory.PAdicHodge.logOnePlus_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:25.084966+00:00
-- url     : https://prove2.me/submissions/2701cd61-26df-404b-8326-f1a3a8bd0225

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_mem

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
variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) : logOnePlus I z hz ∈ I :=
  seriesEval_mem hz constantCoeff_log
end GroundTheory.PAdicHodge
