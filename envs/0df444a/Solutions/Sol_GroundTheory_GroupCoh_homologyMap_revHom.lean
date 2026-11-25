-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_revHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:19.033107+00:00
-- url     : https://prove2.me/submissions/3662cd62-05ab-4c4e-9b77-a41760864612

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Theorems.Thm_GroundTheory_GroupCoh_revHom_naturality
import Theorems.Thm_GroundTheory_GroupCoh_revHom_f_zero
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_eq_id_of_f_eq_id
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) (A : Rep k G) :
    HomologicalComplex.homologyMap (revHom A) n = 𝟙 _ := by
  induction n generalizing A with
  | zero => exact homologyMap_eq_id_of_f_eq_id _ 0 revHom_f_zero
  | succ n ih =>
    have hS := coindSES_shortExact A
    have hz : IsZero (groupCohomology (coindSES.obj A).X₂ (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (coindIso _ (n + 1))
    have := epi_δ_of_isZero hS n hz
    let Φ : (coindSES.obj A).map (cochainsFunctor k G) ⟶
        (coindSES.obj A).map (cochainsFunctor k G) :=
      { τ₁ := revHom _
        τ₂ := revHom _
        τ₃ := revHom _
        comm₁₂ := revHom_naturality _
        comm₂₃ := revHom_naturality _ }
    have key := HomologicalComplex.HomologySequence.δ_naturality Φ
      (map_cochainsFunctor_shortExact hS) (map_cochainsFunctor_shortExact hS) n (n + 1) rfl
    have h3 : HomologicalComplex.homologyMap Φ.τ₃ n = 𝟙 _ := ih _
    rw [h3, Category.id_comp] at key
    refine (cancel_epi (δ hS n (n + 1) rfl)).1 ?_
    exact key.trans (Category.comp_id _).symm
end GroundTheory.GroupCoh
