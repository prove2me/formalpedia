-- Prove2me | solution 1 for GroundTheory.GroupCoh.inflation_two_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:24.600546+00:00
-- url     : https://prove2.me/submissions/e54e4089-e05b-4558-8f1c-5207ee0c78c2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_inflation_injective

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
theorem _root_.solution (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    Function.Injective (inflation A S 2).hom :=
  inflation_injective two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1
end GroundTheory.GroupCoh
