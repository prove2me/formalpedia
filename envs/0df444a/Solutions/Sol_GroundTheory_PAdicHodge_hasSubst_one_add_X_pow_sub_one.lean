-- Prove2me | solution 1 for GroundTheory.PAdicHodge.hasSubst_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.377438+00:00
-- url     : https://prove2.me/submissions/41a5e5d3-0d0b-415f-9d33-babefa3ad618

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution (q : ℕ) : HasSubst ((1 + X : ℚ⟦X⟧) ^ q - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)
end GroundTheory.PAdicHodge
