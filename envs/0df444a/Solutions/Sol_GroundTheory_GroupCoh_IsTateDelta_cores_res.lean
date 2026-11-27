-- Prove2me | solution 1 for GroundTheory.GroupCoh.IsTateDelta.cores_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:18.473025+00:00
-- url     : https://prove2.me/submissions/460fae1d-1daf-484c-b5d4-1aea6c4e594e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_sq_comp
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
open GroundTheory.GroupCoh.IsTateDelta
variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]
namespace GroundTheory.GroupCoh.IsTateDelta
theorem _root_.solution : IsTateDelta (fun n => tateCores (k := k) U n ≫ tateRes V n) := by
  intro X hX n
  exact sq_comp (tateCores_δ U hX n) (tateRes_δ V hX n)
end GroundTheory.GroupCoh.IsTateDelta
