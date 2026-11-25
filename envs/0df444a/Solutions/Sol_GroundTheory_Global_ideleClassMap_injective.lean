-- Prove2me | solution 1 for GroundTheory.Global.ideleClassMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:18.716605+00:00
-- url     : https://prove2.me/submissions/6a40fd9c-09e3-4b77-bec4-4dbf726dc973

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_ideleClassMap_mk
import Theorems.Thm_GroundTheory_Global_mem_range_diagonal_of_ideleEmbedding
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ker_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


attribute [local simp] GroundTheory.Global.ideleClassMap_mk

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
namespace GroundTheory.Global
theorem _root_.solution : Function.Injective (ideleClassMap K L) := by
  refine (injective_iff_map_eq_one _).2 fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ← MonoidHom.mem_ker, IdeleClassGroup.ker_mk] at hc
  rw [← MonoidHom.mem_ker, IdeleClassGroup.ker_mk]
  exact mem_range_diagonal_of_ideleEmbedding hc
end GroundTheory.Global
