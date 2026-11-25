-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateIndIso_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:59:50.417363+00:00
-- url     : https://prove2.me/submissions/c31be455-3ab6-466a-81b1-d6a40ce6e15f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_CoresRes

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
variable [Fintype G] (S : Subgroup G) [Fintype S]
open scoped Classical
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv :=
  rfl
end GroundTheory.GroupCoh
