-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupCohomology_res_augIdeal_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:16:27.195686+00:00
-- url     : https://prove2.me/submissions/fed69a17-670f-4bd0-8cbd-6b55fd63d24e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_eq_zero_of_isZero
import Theorems.Thm_GroundTheory_GroupCoh_isZero_of_forall_eq_zero
import Theorems.Thm_GroundTheory_GroupCoh_isZero_H1_trivial_int
import Theorems.Thm_GroundTheory_GroupCoh_isZero_groupCohomology_res_leftRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution :
    IsZero (groupCohomology (res S.subtype (augIdeal ℤ G)) 2) := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 1 2 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 1
      (isZero_groupCohomology_res_leftRegular S 2)
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep x
  have hz : IsZero (groupCohomology (res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
    isZero_H1_trivial_int (H := S)
  exact (congrArg _ (eq_zero_of_isZero hz z)).trans (map_zero _)
end GroundTheory.GroupCoh
