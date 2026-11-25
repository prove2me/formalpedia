-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCoindIso_inv_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:56.543824+00:00
-- url     : https://prove2.me/submissions/efdc141e-a706-4cec-9f67-ea2006a9f059

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateCoindIso_inv

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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
variable [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).inv.hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) := by
  rw [tateCoindIso_inv]
  exact homologyMap_tateShapiroMap_tateZeroClass S B y
end GroundTheory.GroupCoh
