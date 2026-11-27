-- Prove2me | solution 1 for GroundTheory.Automorphic.lieGroup_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:26.666196+00:00
-- url     : https://prove2.me/submissions/22fabd2f-5e2a-43b7-a1ca-0c5284b33eed

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
open scoped Matrix.Norms.L2Operator
namespace GroundTheory.Automorphic
theorem _root_.solution (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := inferInstance
end GroundTheory.Automorphic
