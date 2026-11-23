-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_mem_wordSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:49.830465+00:00
-- url     : https://prove2.me/submissions/79aeca3b-cb8a-4dc8-9ac6-92a5c5c93bc0

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
theorem _root_.solution {P : Fin n × Fin n → Prop} {w : List (Fin n × Fin n)}
    (hw : ∀ a ∈ w, P a) : word w ∈ wordSpan P w.length :=
  Submodule.subset_span ⟨w, hw, rfl, rfl⟩
end GroundTheory.Automorphic.HarishChandra
