-- Prove2me | solution 1 for GroundTheory.LocalField.augmentation_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.671141+00:00
-- url     : https://prove2.me/submissions/f21ac3a9-3d90-4dec-8e75-da1aeb848b13

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_augMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}
namespace GroundTheory.LocalField
theorem _root_.solution : augmentation G M = (augMap G M).range := by
  classical
  apply le_antisymm
  · rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    refine ⟨Pi.mulSingle g x, ?_⟩
    rw [augMap_apply, Fintype.prod_eq_single g (fun h hh => by simp [Pi.mulSingle_eq_of_ne hh])]
    simp
  · rintro _ ⟨m, rfl⟩
    exact Subgroup.prod_mem _ fun g _ => Subgroup.subset_closure ⟨g, m g, rfl⟩
end GroundTheory.LocalField
