-- Prove2me | solution 1 for GroundTheory.GroupCoh.cohTrivial_of_isZero_of_isZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:18.609825+00:00
-- url     : https://prove2.me/submissions/de549f98-d969-4cc1-8d13-185c2ae512d2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_cohTrivial_of_isZero_of_isZero

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
variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    CohTrivial A :=
  (tateAcyclic_cohTrivial_of_isZero_of_isZero hG A q h₁ h₂).2
end GroundTheory.GroupCoh
