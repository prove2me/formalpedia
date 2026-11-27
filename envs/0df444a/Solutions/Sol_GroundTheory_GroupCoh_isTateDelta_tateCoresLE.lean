-- Prove2me | solution 1 for GroundTheory.GroupCoh.isTateDelta_tateCoresLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:44.477289+00:00
-- url     : https://prove2.me/submissions/e20342a2-04a3-41cc-932e-4f0e2ead4060

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55
import Theorems.Thm_GroundTheory_GroupCoh_sq_comp
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42


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
variable {U W : Subgroup G} (h : W ≤ U)
variable [Fintype U] [Fintype W]
namespace GroundTheory.GroupCoh
theorem _root_.solution : IsTateDelta (tateCoresLE (k := k) h) := by
  let _ := fintypeSubgroupOf h
  intro X hX n
  have hW := shortExact_map_resFunctor W hX
  have hU := shortExact_map_resFunctor U hX
  have h1 := tateTransport_δ (Subgroup.subgroupOfEquivOfLe h) hW n
  have h2 := tate_whiskerRight_δ (coresLENatTrans (k := k) h)
    (shortExact_map_resFunctor_equiv (Subgroup.subgroupOfEquivOfLe h) hW)
    (shortExact_map_resFunctor (W.subgroupOf U) hU) n
  have h3 := tateCores_δ (W.subgroupOf U) hU n
  exact sq_comp h1 (sq_comp h2 h3)
end GroundTheory.GroupCoh
