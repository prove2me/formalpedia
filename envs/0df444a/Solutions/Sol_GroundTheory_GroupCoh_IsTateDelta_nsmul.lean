-- Prove2me | solution 1 for GroundTheory.GroupCoh.IsTateDelta.nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:36.148815+00:00
-- url     : https://prove2.me/submissions/746891ba-a685-4f60-bf36-5379ca5e3b07

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_sq_nsmul

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
omit [Fintype G]
namespace GroundTheory.GroupCoh.IsTateDelta
theorem _root_.solution (m : ℕ)
    {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) : IsTateDelta (fun n => m • α n) := by
  intro X hX n
  rw [NatTrans.app_nsmul, NatTrans.app_nsmul]
  exact sq_nsmul m (hα hX n)
end GroundTheory.GroupCoh.IsTateDelta
