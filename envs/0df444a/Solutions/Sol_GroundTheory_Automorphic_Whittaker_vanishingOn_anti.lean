-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.vanishingOn_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:31.981745+00:00
-- url     : https://prove2.me/submissions/726599ff-aad1-40e6-9e5c-4658c11abd4b

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
theorem _root_.solution {Z Z' : Set X} (h : Z ⊆ Z') : vanishingOn Z' ≤ vanishingOn Z :=
  fun _ hf x hx => hf x (h hx)
end GroundTheory.Automorphic.Whittaker
