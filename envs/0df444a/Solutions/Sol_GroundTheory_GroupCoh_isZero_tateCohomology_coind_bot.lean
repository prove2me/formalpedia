-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_coind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:28.056068+00:00
-- url     : https://prove2.me/submissions/e850ad8f-8211-477e-9d98-e1688793f0e0

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_neg_one_of_sum_eq
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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k (⊥ : Subgroup G))
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm
end GroundTheory.GroupCoh
