-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateResLE_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:18.33652+00:00
-- url     : https://prove2.me/submissions/80a865d8-bf12-477e-8a42-cf270d6d784c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyFunctor_map_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateRes_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateTransport_tateZeroClass


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
theorem _root_.solution (A : Rep.{u} k G) (y : (res U.subtype A).ρ.invariants) :
    ((tateResLE h 0).app A).hom (tateZeroClass (res U.subtype A) y) =
      tateZeroClass (res W.subtype A) (invariantsLE h y) := by
  let _ := fintypeSubgroupOf h
  have e1 := tateRes_tateZeroClass (W.subgroupOf U) (res U.subtype A) y
  have e2 := tateTransport_tateZeroClass (Subgroup.subgroupOfEquivOfLe h).symm
    (res (W.subgroupOf U).subtype (res U.subtype A)) (invariantsRes (W.subgroupOf U).subtype y)
  have e3 := tateCohomologyFunctor_map_tateZeroClass ((resLENatTrans (k := k) h).app A)
    (invariantsTransport (Subgroup.subgroupOfEquivOfLe h).symm
      (invariantsRes (W.subgroupOf U).subtype y))
  refine (congrArg (fun z => ((tateCohomologyFunctor 0).map ((resLENatTrans (k := k) h).app A)).hom
    (((tateTransport (Subgroup.subgroupOfEquivOfLe h).symm 0).app
      (res (W.subgroupOf U).subtype (res U.subtype A))).hom z)) e1).trans ?_
  refine (congrArg (fun z => ((tateCohomologyFunctor 0).map ((resLENatTrans (k := k) h).app A)).hom z)
    e2).trans ?_
  exact e3
end GroundTheory.GroupCoh
