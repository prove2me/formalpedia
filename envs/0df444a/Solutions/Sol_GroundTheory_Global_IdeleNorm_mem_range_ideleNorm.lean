-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.mem_range_ideleNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:44.261618+00:00
-- url     : https://prove2.me/submissions/7ec41150-3ca4-4dd2-805b-6187f1382a94

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Theorems.Thm_GroundTheory_Global_IdeleNorm_ideleNorm_glue
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorHomeomorph_apply
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
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_ideleClassMap_mk
import Theorems.Thm_GroundTheory_Global_ideleClassNorm_mk
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
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.ideleClassMap_mk
attribute [local simp] GroundTheory.Global.ideleClassNorm_mk
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range)
    (hint : ∀ᶠ v in cofinite,
      IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)) :
    x ∈ (ideleNorm K L).range := by
  classical
  let yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ :=
    fun v ↦ if h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
      then (Subgroup.mem_map.1 h).choose else (MonoidHom.mem_range.1 (hfin v)).choose
  have hyf_int : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v := hint.mono fun v h ↦ by
    simp only [yf, dif_pos h]
    exact (Subgroup.mem_map.1 h).choose_spec.1
  have hyf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x := by
    intro v
    by_cases h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
    · simp only [yf, dif_pos h]
      exact (Subgroup.mem_map.1 h).choose_spec.2
    · simp only [yf, dif_neg h]
      exact (MonoidHom.mem_range.1 (hfin v)).choose_spec
  exact ⟨glue yf hyf_int (fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose),
    ideleNorm_glue _ _ _ hyf fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose_spec⟩
end GroundTheory.Global.IdeleNorm
