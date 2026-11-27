-- Prove2me | solution 2 for GroundTheory.Automorphic.HarishChandra.filt_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:02.182362+00:00
-- url     : https://prove2.me/submissions/63655b76-b1f0-4b45-b102-74c1ef471d23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {d d' : ℕ} (h : d ≤ d') : filt (n := n) d ≤ filt d' :=
  Submodule.span_mono fun _ ⟨w, hw, hu⟩ => ⟨w, hw.trans h, hu⟩
end GroundTheory.Automorphic.HarishChandra
