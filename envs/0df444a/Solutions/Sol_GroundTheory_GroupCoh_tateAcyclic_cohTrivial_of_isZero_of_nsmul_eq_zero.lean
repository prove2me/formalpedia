-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:26.919446+00:00
-- url     : https://prove2.me/submissions/e063f03a-b523-4099-bdba-3ec9f2b0945b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_coindShift
import Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_indShift
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_cohTrivial_of_isZero_of_shift


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
open CategoryTheory Limits Rep groupHomology
universe u
variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) (q : ℤ)
    (hq : IsZero (tateCohomology M q)) : TateAcyclic M ∧ CohTrivial M :=
  tateAcyclic_cohTrivial_of_isZero_of_shift (fun M => ∀ x : M, p • x = 0)
    (fun M hM => nsmul_eq_zero_coindShift M hM) (fun M hM => nsmul_eq_zero_indShift M hM)
    (fun M hM h => tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero hG M hM h) q M hM hq
end GroundTheory.GroupCoh
