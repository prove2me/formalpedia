-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.wordSpan_le_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:26.576124+00:00
-- url     : https://prove2.me/submissions/a115ca95-a818-4aca-9fb4-2b89ebcd21bb

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
theorem _root_.solution (P : Fin n × Fin n → Prop) (k : ℕ) : wordSpan (n := n) P k ≤ filt k :=
  Submodule.span_le.2 fun _ ⟨w, _, hw, hu⟩ => Submodule.subset_span ⟨w, hw.le, hu⟩
end GroundTheory.Automorphic.HarishChandra
