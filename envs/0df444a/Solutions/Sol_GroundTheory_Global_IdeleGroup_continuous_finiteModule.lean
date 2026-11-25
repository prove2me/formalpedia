-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_finiteModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:53.785617+00:00
-- url     : https://prove2.me/submissions/6f1da6f8-f8a3-4139-a25e-5afd8fb508d8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteModule_eq_one_of_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_standardOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : Continuous (finiteModule (K := K)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hU : (fun y ↦ x⁻¹ * y) ⁻¹' (standardOpenSubgroup K : Set (IdeleGroup K)) ∈ 𝓝 x :=
    ((isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [(standardOpenSubgroup K).one_mem])
  refine (continuousAt_const (y := finiteModule x)).congr ?_
  filter_upwards [hU] with y hy
  rw [← mul_inv_cancel_left x y, finiteModule_mul, finiteModule_eq_one_of_mem hy, mul_one]
end GroundTheory.Global.IdeleGroup
