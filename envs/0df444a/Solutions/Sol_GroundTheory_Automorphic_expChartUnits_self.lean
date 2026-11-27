-- Prove2me | solution 1 for GroundTheory.Automorphic.expChartUnits_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:21.654209+00:00
-- url     : https://prove2.me/submissions/d37026c5-b28b-43a5-93a4-4d17d9bbec78

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Theorems.Thm_GroundTheory_Automorphic_expPartialHomeomorph_symm_one

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
theorem _root_.solution (g : 𝔸ˣ) : expChartUnits 𝕂 g g = 0 := by
  show (𝔢).symm ((g⁻¹ * g : 𝔸ˣ) : 𝔸) = 0
  simpa using expPartialHomeomorph_symm_one 𝕂 𝔸
end GroundTheory.Automorphic
