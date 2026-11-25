-- Prove2me | solution 1 for GroundTheory.Automorphic.traceForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:44.19746+00:00
-- url     : https://prove2.me/submissions/097c2ba3-5e53-4ac4-8569-bf091c9773a8

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
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}
namespace GroundTheory.Automorphic
theorem _root_.solution (X Y : L) :
    traceForm L X Y = RCLike.re (trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))) := rfl
end GroundTheory.Automorphic
