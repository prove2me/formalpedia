-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_vanishingOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:12.265642+00:00
-- url     : https://prove2.me/submissions/7d84b798-0717-45d2-a95e-4cd41a63879f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {Z : Set X} {f : X → ℂ} : f ∈ vanishingOn Z ↔ ∀ x ∈ Z, f x = 0 :=
  Iff.rfl
end GroundTheory.Automorphic.Whittaker
