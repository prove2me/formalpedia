-- Prove2me | solution 1 for GroundTheory.Automorphic.exp_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:30.619853+00:00
-- url     : https://prove2.me/submissions/e7edf915-efd3-4a81-85e4-f4f83dfd1033

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_refl


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
theorem _root_.solution {X : Matrix ι ι 𝕜} (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hX,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
    NormedSpace.exp_zero]
end GroundTheory.Automorphic
