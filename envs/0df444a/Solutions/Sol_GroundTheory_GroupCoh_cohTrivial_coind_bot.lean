-- Prove2me | solution 1 for GroundTheory.GroupCoh.cohTrivial_coind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:49.315193+00:00
-- url     : https://prove2.me/submissions/b189e4c7-2a4a-4dc5-98e2-8040147bf415

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_sum_coindBotProj


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
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (coind (⊥ : Subgroup G).subtype B) :=
  cohTrivial_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
end GroundTheory.GroupCoh
