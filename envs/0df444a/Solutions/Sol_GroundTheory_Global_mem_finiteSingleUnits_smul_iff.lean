-- Prove2me | solution 1 for GroundTheory.Global.mem_finiteSingleUnits_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:09.051373+00:00
-- url     : https://prove2.me/submissions/ab7ed690-7d60-4592-b333-246828dbc223

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_coe_finiteSingleUnits
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_mem_integralFiniteAdeles
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

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ)
    (y : 𝔸ᶠ[K]) :
    y ∈ finiteSingleUnits v z • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      (∀ w ≠ v, y w ∈ w.adicCompletionIntegers K) ∧
        (z : v.adicCompletion K)⁻¹ * y v ∈ v.adicCompletionIntegers K := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, ← map_inv, SetLike.mem_coe,
    mem_integralFiniteAdeles, coe_finiteSingleUnits]
  have hc : ∀ w, (IdeleGroup.finiteAdeleSingle v ((z⁻¹ : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) * y) w = IdeleGroup.finiteAdeleSingle v
        ((z⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w * y w := fun w ↦ rfl
  constructor
  · intro h
    refine ⟨fun w hw ↦ ?_, ?_⟩
    · have := h w
      rwa [hc, IdeleGroup.finiteAdeleSingle_apply_of_ne hw, one_mul] at this
    · have := h v
      rwa [hc, IdeleGroup.finiteAdeleSingle_apply_self, Units.val_inv_eq_inv_val] at this
  · rintro ⟨h1, h2⟩ w
    rw [hc]
    by_cases hw : w = v
    · subst hw
      rwa [IdeleGroup.finiteAdeleSingle_apply_self, Units.val_inv_eq_inv_val]
    · rw [IdeleGroup.finiteAdeleSingle_apply_of_ne hw, one_mul]
      exact h1 w hw
end GroundTheory.Global
