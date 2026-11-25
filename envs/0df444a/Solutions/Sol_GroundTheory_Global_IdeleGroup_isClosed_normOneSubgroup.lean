-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isClosed_normOneSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:26.277237+00:00
-- url     : https://prove2.me/submissions/8aff94cd-e158-48be-9fa8-d0b817bec0ca

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ideleModule
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_normOneSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
variable (K)
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : IsClosed (normOneSubgroup K : Set (IdeleGroup K)) := by
  have h : (normOneSubgroup K : Set (IdeleGroup K)) =
      (fun x ↦ (ideleModule K x : ℝ)) ⁻¹' {1} := by
    ext x
    exact mem_normOneSubgroup
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_ideleModule)
end GroundTheory.Global.IdeleGroup
