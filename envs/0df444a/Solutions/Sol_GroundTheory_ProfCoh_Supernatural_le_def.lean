-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.le_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:33.78343+00:00
-- url     : https://prove2.me/submissions/a6cf1942-b556-4878-be10-8fdc8a621a04

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := Iff.rfl
end GroundTheory.ProfCoh.Supernatural
