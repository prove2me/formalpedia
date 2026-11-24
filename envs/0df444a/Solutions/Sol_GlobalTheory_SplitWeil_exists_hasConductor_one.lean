-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_hasConductor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:09:42.608137+00:00
-- url     : https://prove2.me/submissions/85566715-622e-45e5-be82-9a5d910acdcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_mem_cball_uniformiser
import Theorems.Thm_GlobalTheory_SplitWeil_ratCircle_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable (k)
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  let A := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk (ϖ : k)⁻¹ : k ⧸ A) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    have h' : valuation k (ϖ : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).mp h
    rw [map_inv₀, inv_le_one₀ (by simp [zero_lt_iff, h0])] at h'
    exact absurd hϖ1 (not_lt.mpr h')
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let χ : k →+ AddCircle (1 : ℝ) := ratCircle.comp (AddMonoidHom.comp c (QuotientAddGroup.mk' A))
  refine ⟨AddCircle.toCircle_addChar.compAddMonoidHom χ, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    rw [Units.val_one, map_one, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxi : valuation k x⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h1 := (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨x⁻¹, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
    have h2 : valuation k x⁻¹ ≤ valuation k (ϖ : k) := h1
    have h3 := h (ϖ : k)⁻¹ (by
      rw [map_inv₀] at h2 ⊢
      exact inv_le_of_inv_le₀ (by simp [zero_lt_iff, hx0]) h2)
    have h4 : AddCircle.toCircle (χ (ϖ : k)⁻¹) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h3
    exact hc (ratCircle_eq_zero (AddCircle.injective_toCircle one_ne_zero h4))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ A) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact (Valuation.mem_integer_iff _ _).mpr (by simpa using hy.trans h)
    have : χ y = 0 := by
      show ratCircle (c (QuotientAddGroup.mk y)) = 0
      rw [hy', map_zero, map_zero]
    show AddCircle.toCircle (χ y) = 1
    rw [this, AddCircle.toCircle_zero]
end GlobalTheory.SplitWeil
