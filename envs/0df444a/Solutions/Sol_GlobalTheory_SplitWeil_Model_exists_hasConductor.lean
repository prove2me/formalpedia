-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.exists_hasConductor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:06.073808+00:00
-- url     : https://prove2.me/submissions/1c814c72-c55f-4ad4-871c-b761ed312435

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_ratCircle_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)⁻¹
  have ht1 : 1 < valuation k t := by
    rw [ht]; exact uniformizer_inv_le_iff.1 le_rfl
  let O : AddSubgroup k := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk t : k ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact not_le.2 ht1
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : (k ⧸ O) →+ AddCircle (1 : ℚ) := c
  let f : k →+ AddCircle (1 : ℝ) := ratCircle.comp (c'.comp (QuotientAddGroup.mk' O))
  refine ⟨(AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom f, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    have hx' : 1 < valuation k x := by simpa using hx
    have h1 := h t (ht ▸ uniformizer_inv_le_iff.2 hx')
    have h2 : AddCircle.toCircle (f t) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero h2))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ O) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hy.trans (by simpa using h)
    show AddCircle.toCircle (ratCircle (c' (QuotientAddGroup.mk y))) = 1
    rw [hy']; simp
end GlobalTheory.SplitWeil.Model
