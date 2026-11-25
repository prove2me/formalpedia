-- Prove2me | solution 1 for GroundTheory.Global.neg_ne_zero_of_one_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:45.911837+00:00
-- url     : https://prove2.me/submissions/23cb9bef-5213-4992-8cdb-5475b8f0eb97

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) : -s ≠ 0 :=
  neg_ne_zero.2 fun h ↦ by
    rw [h, zero_re] at hs
    linarith
end GroundTheory.Global
