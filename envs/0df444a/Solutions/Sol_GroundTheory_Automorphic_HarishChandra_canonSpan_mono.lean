-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canonSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:49.628402+00:00
-- url     : https://prove2.me/submissions/3c5c4e6c-6edf-4849-b974-0d60834db28b

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
theorem _root_.solution {P : Fin n × Fin n → Prop} {lo lo' hi hi' : ℕ} (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : canonSpan P lo hi ≤ canonSpan P lo' hi' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, h1, h2, rfl⟩
  exact ⟨m, hm, hlo.trans h1, h2.trans hhi, rfl⟩
end GroundTheory.Automorphic.HarishChandra
