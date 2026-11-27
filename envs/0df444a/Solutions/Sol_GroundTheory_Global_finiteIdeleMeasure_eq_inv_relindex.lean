-- Prove2me | solution 1 for GroundTheory.Global.finiteIdeleMeasure_eq_inv_relindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:24.426796+00:00
-- url     : https://prove2.me/submissions/f0e4703e-5b13-496d-85e9-b6efbf8b3126

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
import Theorems.Thm_GroundTheory_Global_finiteIdeleMeasure_finiteIntegralUnits
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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) (hW : W ≤ finiteIntegralUnits K) :
    finiteIdeleMeasure K W = ((W.relIndex (finiteIntegralUnits K) : ℕ) : ℝ≥0∞)⁻¹ := by
  set H := finiteIntegralUnits K
  have hHm : MeasurableEmbedding (Subtype.val : H → (FiniteAdeleRing (𝓞 K) K)ˣ) :=
    MeasurableEmbedding.subtype_coe (isOpen_finiteIntegralUnits K).measurableSet
  set μ' : Measure H := Measure.comap Subtype.val (finiteIdeleMeasure K)
  have hinv : μ'.IsMulLeftInvariant := by
    refine ⟨fun g ↦ Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply (measurable_const_mul g) hs, hHm.comap_apply, hHm.comap_apply]
    have : Subtype.val '' ((fun x : H ↦ g * x) ⁻¹' s) =
        (fun x ↦ (g : (FiniteAdeleRing (𝓞 K) K)ˣ) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨g⁻¹ * y, by simpa using hy, ?_⟩
        simp [hyx]
    rw [this, measure_preimage_mul]
  have hc : CompactSpace H := isCompact_iff_compactSpace.1 (isCompact_finiteIntegralUnits K)
  have hWHo : IsOpen ((W.subgroupOf H : Subgroup H) : Set H) :=
    hWo.preimage continuous_subtype_val
  have : Finite (H ⧸ W.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hWHo
  have : (W.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h := Subgroup.index_mul_measure (W.subgroupOf H) hWHo.measurableSet μ'
  have h1 : μ' Set.univ = 1 := by
    rw [hHm.comap_apply, Set.image_univ, Subtype.range_coe]
    exact finiteIdeleMeasure_finiteIntegralUnits K
  have h2 : μ' (W.subgroupOf H : Set H) = finiteIdeleMeasure K W := by
    rw [hHm.comap_apply]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hW hx⟩, hx, rfl⟩
  rw [h1, h2] at h
  rw [Subgroup.relIndex]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h)
end GroundTheory.Global
