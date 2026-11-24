-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.supportedIn_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:17.211647+00:00
-- url     : https://prove2.me/submissions/9435a1e3-5515-4133-92a9-d69ce9dc604e

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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U V : Set X} (h : U ⊆ V) : supportedIn U ≤ supportedIn V :=
  fun _ hf => ⟨hf.1, hf.2.trans h⟩
end GroundTheory.Automorphic.Whittaker
