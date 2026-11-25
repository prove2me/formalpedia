-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCoindIso_hom_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:27.223852+00:00
-- url     : https://prove2.me/submissions/26e8ff14-0e42-46f9-ab5e-342a3ee96726

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
    (tateCoindIso S B 0).hom.hom (tateZeroClass (coind S.subtype B) (coindConst S B y)) =
      tateZeroClass B y := by
  rw [← homologyMap_tateShapiroMap_tateZeroClass, ← tateCoindIso_inv]
  exact Iso.inv_hom_id_apply (tateCoindIso S B 0) _
end GroundTheory.GroupCoh
