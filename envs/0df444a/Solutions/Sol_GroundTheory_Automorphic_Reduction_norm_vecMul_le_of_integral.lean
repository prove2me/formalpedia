-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_vecMul_le_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:41.28626+00:00
-- url     : https://prove2.me/submissions/0f5f6e50-b87d-4aaa-88dc-8792103827bd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
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
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply

set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers K) (z : Fin n → v.adicCompletion K) :
    ‖z ᵥ* M‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg z) fun i _ => ?_
  rw [norm_mul]
  calc ‖z i‖ * ‖M i j‖ ≤ ‖z i‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_le_one_of_mem v (hM i j)) (norm_nonneg _)
    _ ≤ ‖z‖ := by rw [mul_one]; exact norm_le_pi_norm z i
end GroundTheory.Automorphic.Reduction
