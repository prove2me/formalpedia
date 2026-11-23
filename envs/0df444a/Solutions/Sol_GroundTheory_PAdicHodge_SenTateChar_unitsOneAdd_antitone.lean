-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.unitsOneAdd_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:14.229293+00:00
-- url     : https://prove2.me/submissions/b4981abd-f60b-4be2-8938-05bedca922b4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits

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
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution : Antitone (unitsOneAdd p) := fun _ _ h _ hu =>
  (pow_dvd_pow _ h).trans hu
end GroundTheory.PAdicHodge.SenTateChar
