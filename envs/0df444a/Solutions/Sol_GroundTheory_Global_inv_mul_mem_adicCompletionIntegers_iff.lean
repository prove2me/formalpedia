-- Prove2me | solution 1 for GroundTheory.Global.inv_mul_mem_adicCompletionIntegers_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:15.192446+00:00
-- url     : https://prove2.me/submissions/488559e7-9587-4202-84be-db49da7781ec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_coe_finiteSingleUnits
import Theorems.Thm_GroundTheory_Global_finiteAdeleEval_apply
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
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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


attribute [local simp] GroundTheory.Global.coe_finiteSingleUnits
attribute [local simp] GroundTheory.Global.finiteAdeleEval_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (x : v.adicCompletion K) :
    (ϖ : v.adicCompletion K)⁻¹ * x ∈ v.adicCompletionIntegers K ↔
      ∃ h : x ∈ v.adicCompletionIntegers K, (⟨x, h⟩ : v.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  constructor
  · intro h
    have hx : x = ϖ * ((ϖ : v.adicCompletion K)⁻¹ * x) := (mul_inv_cancel_left₀ hϖ0 x).symm
    have hxO : x ∈ v.adicCompletionIntegers K := by
      rw [hx]
      exact mul_mem ϖ.2 h
    refine ⟨hxO, Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩⟩
    change (ϖ : v.adicCompletion K)⁻¹ * x * ϖ = x
    rw [mul_comm, mul_inv_cancel_left₀ hϖ0]
  · rintro ⟨hx, hm⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
    have hxr : x = r * ϖ := (congrArg Subtype.val hr).symm
    rw [hxr, mul_comm (r : v.adicCompletion K), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
    exact r.2
end GroundTheory.Global
