-- Prove2me | solution 2 for GroundTheory.Automorphic.expChartUnits_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:24.689299+00:00
-- url     : https://prove2.me/submissions/4a5a17d6-d88b-43c8-ad5e-782fd850b465

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
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸
namespace GroundTheory.Automorphic
theorem _root_.solution (g : 𝔸ˣ) (X : 𝔸) :
    (((expChartUnits 𝕂 g).symm X : 𝔸ˣ) : 𝔸) = g * exp X := rfl
end GroundTheory.Automorphic
