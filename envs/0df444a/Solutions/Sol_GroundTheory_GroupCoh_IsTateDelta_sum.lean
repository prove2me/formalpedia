-- Prove2me | solution 1 for GroundTheory.GroupCoh.IsTateDelta.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:38.7195+00:00
-- url     : https://prove2.me/submissions/75fd8af7-eb1c-448d-a177-9bf0775d010d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_sq_sum

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
theorem _root_.solution {ι : Type*} (s : Finset ι)
    {α : ι → ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : ∀ i ∈ s, IsTateDelta (α i)) : IsTateDelta (fun n => ∑ i ∈ s, α i n) := by
  intro X hX n
  rw [NatTrans.app_sum, NatTrans.app_sum]
  exact sq_sum s fun i hi => hα i hi hX n
end GroundTheory.GroupCoh.IsTateDelta
