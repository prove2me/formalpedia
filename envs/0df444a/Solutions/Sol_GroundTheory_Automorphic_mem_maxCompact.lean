-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_maxCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:39.873529+00:00
-- url     : https://prove2.me/submissions/95854e4c-9262-4e48-b611-1a244c6593ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution {G : Subgroup (Matrix ι ι 𝕜)ˣ} {g : G} :
    g ∈ maxCompact G ↔ ((g : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜 :=
  Iff.rfl
end GroundTheory.Automorphic
