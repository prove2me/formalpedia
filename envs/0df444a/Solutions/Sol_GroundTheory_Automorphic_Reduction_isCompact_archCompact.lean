-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.isCompact_archCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:45.589577+00:00
-- url     : https://prove2.me/submissions/85e34294-dde1-4fae-b06d-c566ce5e6842

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_mem_archCompact
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_apply_le_one_of_mem_archCompact
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_euclidNorm
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (w : InfinitePlace K) :
    IsCompact (archCompact (n := n) w : Set (GL (Fin n) w.Completion)) := by
  set T : Set (Matrix (Fin n) (Fin n) w.Completion) := Set.pi univ fun _ => Set.pi univ fun _ =>
    Metric.closedBall (0 : w.Completion) 1 with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall _ _
  have hbig : IsCompact (Units.embedProduct (Matrix (Fin n) (Fin n) w.Completion) ⁻¹'
      (T ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' T))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hTc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hTc))
  refine hbig.of_isClosed_subset ?_ ?_
  · have : (archCompact (n := n) w : Set (GL (Fin n) w.Completion)) = ⋂ y : Fin n → w.Completion,
        {k : GL (Fin n) w.Completion |
          euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y} := by
      ext k
      simp [mem_archCompact]
    rw [this]
    exact isClosed_iInter fun y => isClosed_eq
      (continuous_euclidNorm.comp ((continuous_const.matrix_vecMul Units.continuous_val)))
      continuous_const
  · intro k hk
    refine ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
    · simpa using norm_apply_le_one_of_mem_archCompact hk i j
    · simpa using norm_apply_le_one_of_mem_archCompact ((archCompact w).inv_mem hk) i j
end GroundTheory.Automorphic.Reduction
