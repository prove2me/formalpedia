-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_eq_zsmul_augClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:17:07.567086+00:00
-- url     : https://prove2.me/submissions/856d1825-b5dd-4a7c-b378-7b3466aca003

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
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
theorem _root_.solution (y : groupCohomology (res S.subtype (augIdeal ℤ G)) 1) :
    ∃ m : ℤ, y = m • augClass S := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 0
      (isZero_groupCohomology_res_leftRegular S 1)
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep y
  let c : ℤ := show ℤ from ((H0Iso _).hom w).1
  refine ⟨c, ?_⟩
  have hw : w = (H0Iso _).inv (c • oneInvariant ℤ S.subtype) := by
    have : ((H0Iso _).hom w) = c • oneInvariant ℤ S.subtype := by
      apply Subtype.ext
      change _ = c * 1
      rw [mul_one]
    rw [← this]
    exact ((Iso.hom_inv_id_apply (H0Iso _) w)).symm
  conv_lhs => rw [hw]
  rw [map_zsmul]
  exact map_zsmul _ c _
end GroundTheory.GroupCoh
