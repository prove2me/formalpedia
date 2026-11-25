-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupCohomology_res_splittingModule_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:21.865195+00:00
-- url     : https://prove2.me/submissions/cdf84f62-2d09-4b2c-83ca-7581c7b0993e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_P2M_GroundTheory_GroupCoh_isZero_X__of_injective___4a150f60598f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_split__injective_819166473dcc

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
theorem _root_.solution
    (h1 : IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 1) :=
  isZero_X₂_of_injective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 h1
    (splitδ_injective M u S h2)
end GroundTheory.GroupCoh
