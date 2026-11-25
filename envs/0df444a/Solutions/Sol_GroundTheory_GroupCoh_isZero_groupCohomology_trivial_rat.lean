-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupCohomology_trivial_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:55.262932+00:00
-- url     : https://prove2.me/submissions/fdef2dfd-58be-475d-8502-e29dbd0b0066

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Theorems.Thm_GroundTheory_GroupCoh_isZero_groupCohomology_of_bijective_nsmul
import Theorems.Thm_GroundTheory_GroupCoh_bijective_nsmul_of_module_rat

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
variable {G : Type} [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n
end GroundTheory.GroupCoh
