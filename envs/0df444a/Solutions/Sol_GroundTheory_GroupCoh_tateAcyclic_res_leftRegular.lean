-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:40:32.644272+00:00
-- url     : https://prove2.me/submissions/c13a66f8-947f-4646-a403-676e84435302

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_leftRegular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution : TateAcyclic (res S.subtype (Rep.leftRegular ℤ G)) :=
  cohTrivial_leftRegular ℤ G S
end GroundTheory.GroupCoh
