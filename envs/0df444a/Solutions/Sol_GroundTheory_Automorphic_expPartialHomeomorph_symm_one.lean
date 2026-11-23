-- Prove2me | solution 1 for GroundTheory.Automorphic.expPartialHomeomorph_symm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:07.899893+00:00
-- url     : https://prove2.me/submissions/9165673d-7a49-4af5-baa6-dc498cac7ef0

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
variable (𝕂 : Type*) [RCLike 𝕂] (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution : (expPartialHomeomorph 𝕂 𝔸).symm 1 = 0 := by
  simpa [coe_expPartialHomeomorph] using
    (expPartialHomeomorph 𝕂 𝔸).left_inv (zero_mem_expPartialHomeomorph_source 𝕂 𝔸)
end GroundTheory.Automorphic
