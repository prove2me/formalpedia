-- Prove2me | solution 1 for GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:12.537043+00:00
-- url     : https://prove2.me/submissions/9d5a0583-9cb9-4657-a85e-25f84af7af30

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_range_inflation_eq_ker_restriction

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
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
variable {A S}
namespace GroundTheory.GroupCoh
theorem _root_.solution
    (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    LinearMap.range (inflation A S 2).hom = LinearMap.ker (restriction A S 2).hom :=
  range_inflation_eq_ker_restriction two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1
end GroundTheory.GroupCoh
