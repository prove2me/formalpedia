-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:46.937801+00:00
-- url     : https://prove2.me/submissions/bb3f256b-fdaa-4b70-be94-6297c4c39fcc

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
theorem _root_.solution {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U :=
  Iff.rfl
end GroundTheory.Automorphic.Whittaker
