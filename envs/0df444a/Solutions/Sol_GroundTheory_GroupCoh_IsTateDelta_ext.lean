-- Prove2me | solution 1 for GroundTheory.GroupCoh.IsTateDelta.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:45.462306+00:00
-- url     : https://prove2.me/submissions/778f45d0-763e-4619-8c04-9b536a1adfdb

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_tate_natTrans_eq_of_eq_zero
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_res_indSES_X__55c5a5530310


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
theorem _root_.solution {α β : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) (h0 : α 0 = β 0) : α = β :=
  funext (tate_natTrans_eq_of_eq_zero (resFunctor U.subtype) (resFunctor V.subtype)
    (shortExact_map_resFunctor U) (shortExact_map_resFunctor V)
    (tateAcyclic_res_coindSES_X₂ U) (tateAcyclic_res_indSES_X₂ V) α β hα hβ h0)
end GroundTheory.GroupCoh.IsTateDelta
