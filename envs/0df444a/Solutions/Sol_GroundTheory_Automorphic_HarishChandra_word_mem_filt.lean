-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_mem_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:27.4187+00:00
-- url     : https://prove2.me/submissions/473ba080-3b4d-4097-9a92-da35a75fad3f

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
theorem _root_.solution {w : List (Fin n × Fin n)} {d : ℕ} (h : w.length ≤ d) : word w ∈ filt (n := n) d :=
  Submodule.subset_span ⟨w, h, rfl⟩
end GroundTheory.Automorphic.HarishChandra
