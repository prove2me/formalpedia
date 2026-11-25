-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mem_canonSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:46.63339+00:00
-- url     : https://prove2.me/submissions/1e48c12b-f2e1-43c7-9e3d-ad0b8c56d064

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
theorem _root_.solution {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) : canon m ∈ canonSpan P m.degree m.degree :=
  Submodule.subset_span ⟨m, hm, le_rfl, le_rfl, rfl⟩
end GroundTheory.Automorphic.HarishChandra
