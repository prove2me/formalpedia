-- Prove2me | solution 1 for GroundTheory.Global.integral_normOneMeasure_eq_setIntegral_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:30.402632+00:00
-- url     : https://prove2.me/submissions/120a014b-a8e1-44e4-b336-ce76284c3554

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : normOneSubgroup K → E} (hf : Integrable f (normOneMeasure K)) :
    ∫ u, f u ∂normOneMeasure K = ∫ u in normOneFundamentalDomain K,
      ∑' ξ : Kˣ, f (diagonalToNormOne K ξ * u) ∂normOneMeasure K := by
  have h𝓕 := isFundamentalDomain_normOneFundamentalDomain K (normOneMeasure K)
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, ∀ u, f (diagonalToNormOne K ξ * u) = f (e ξ • u) := fun ξ u ↦ by
    change f (diagonalToNormOne K ξ * u) = f (u * diagonalToNormOne K ξ)
    rw [mul_comm]
  calc ∫ u, f u ∂normOneMeasure K
      = ∑' γ : (diagonalNormOne K).op, ∫ u in normOneFundamentalDomain K, f (γ • u)
          ∂normOneMeasure K := h𝓕.integral_eq_tsum'' f hf
    _ = ∫ u in normOneFundamentalDomain K, ∑' γ : (diagonalNormOne K).op, f (γ • u)
          ∂normOneMeasure K := by
        rw [integral_tsum]
        · exact fun γ ↦ (hf.1.comp_quasiMeasurePreserving
            (measurePreserving_smul γ (normOneMeasure K)).quasiMeasurePreserving).restrict
        · rw [← h𝓕.lintegral_eq_tsum'' (‖f ·‖ₑ)]
          exact ne_of_lt hf.2
    _ = ∫ u in normOneFundamentalDomain K, ∑' ξ : Kˣ, f (diagonalToNormOne K ξ * u)
          ∂normOneMeasure K := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
        simp only [he]
        exact (e.tsum_eq (fun γ ↦ f (γ • u))).symm
end GroundTheory.Global
