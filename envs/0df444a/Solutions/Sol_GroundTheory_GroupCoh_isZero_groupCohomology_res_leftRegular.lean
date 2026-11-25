-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupCohomology_res_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:56.484829+00:00
-- url     : https://prove2.me/submissions/04baa127-a1f6-47ff-a84f-212aad232af4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_leftRegular
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso


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
theorem _root_.solution (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (res S.subtype (Rep.leftRegular ℤ G)) n) :=
  ((tateAcyclic_res_leftRegular S) n).of_iso (tateIsoH _ n n rfl).symm
end GroundTheory.GroupCoh
