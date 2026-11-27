-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCoresLE_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:26.01143+00:00
-- url     : https://prove2.me/submissions/059b7e64-4133-4f8b-9695-c9d95e6a6de9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyFunctor_map_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateCores_tateZeroClass
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
theorem _root_.solution (A : Rep.{u} k G) (y : (res W.subtype A).ρ.invariants) :
    ((tateCoresLE h 0).app A).hom (tateZeroClass (res W.subtype A) y) =
      tateZeroClass (res U.subtype A) (transferInv (W.subgroupOf U) (invariantsSubgroupOf U y)) := by
  let _ := fintypeSubgroupOf h
  have e1 := tateTransport_tateZeroClass (Subgroup.subgroupOfEquivOfLe h) (res W.subtype A) y
  have e2 := tateCohomologyFunctor_map_tateZeroClass ((coresLENatTrans (k := k) h).app A)
    (invariantsTransport (Subgroup.subgroupOfEquivOfLe h) y)
  have e3 := tateCores_tateZeroClass (W.subgroupOf U) (res U.subtype A) (invariantsSubgroupOf U y)
  refine (congrArg (fun z => ((tateCores (W.subgroupOf U) 0).app (res U.subtype A)).hom
    (((tateCohomologyFunctor 0).map ((coresLENatTrans (k := k) h).app A)).hom z)) e1).trans ?_
  refine (congrArg (fun z => ((tateCores (W.subgroupOf U) 0).app (res U.subtype A)).hom z)
    e2).trans ?_
  exact e3
end GroundTheory.GroupCoh
