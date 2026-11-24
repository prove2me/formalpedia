-- Prove2me | solution 1 for GlobalTheory.lintegral_inv_le_of_support_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:06.620801+00:00
-- url     : https://prove2.me/submissions/772a81e1-4e96-499c-86fc-9b7c7d8977eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : H)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hC0 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hLc : IsCompact (C * K⁻¹) := hCc.mul hK.inv
  have hLt : μ (C * K⁻¹) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpre : ∀ y : H, μ ((· * y) ⁻¹' C) = (Measure.modularCharacterFun y : ENNReal) * μ C := by
    intro y
    rw [← Measure.map_apply (measurable_mul_const y) hCm,
      Measure.map_right_mul_eq_modularCharacterFun_smul μ y]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hbound : ∀ y ∈ K, Measure.modularCharacterFun y ≤ (μ (C * K⁻¹)).toNNReal / (μ C).toNNReal := by
    intro y hy
    have hsub : (· * y) ⁻¹' C ⊆ (C * K⁻¹) := by
      intro z hz
      exact ⟨z * y, hz, y⁻¹, by simpa using hy, by simp⟩
    have h1 : (Measure.modularCharacterFun y : ENNReal) * μ C ≤ μ (C * K⁻¹) := (hpre y) ▸ measure_mono hsub
    have hCpos : 0 < (μ C).toNNReal := ENNReal.toNNReal_pos hC0 hCt
    rw [le_div_iff₀ hCpos]
    have := ENNReal.toNNReal_mono hLt h1
    simpa [ENNReal.toNNReal_mul] using this
  refine ⟨(μ (C * K⁻¹)).toNNReal / (μ C).toNNReal, fun φ hφ hsupp => ?_⟩
  have key : ∫⁻ x, φ x ∂μ = ∫⁻ x, (Measure.modularCharacterFun x : ENNReal) * φ x⁻¹ ∂μ := by
    have h := measure_mul_lintegral_eq μ μ hCm φ hφ
    simp_rw [hpre, mul_comm _ (μ C), mul_assoc] at h
    rw [lintegral_const_mul' _ _ hCt] at h
    exact (ENNReal.mul_right_inj hC0 hCt).1 h
  rw [key, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x⁻¹ ∈ K
  · have hb := hbound _ hx
    have hmul : (Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x = 1 := by
      rw [← ENNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel,
        Measure.modularCharacterFun_map_one, ENNReal.coe_one]
    calc φ x⁻¹ = ((Measure.modularCharacterFun x⁻¹ : ENNReal) * Measure.modularCharacterFun x) * φ x⁻¹ := by rw [hmul, one_mul]
      _ = (Measure.modularCharacterFun x⁻¹ : ENNReal) * ((Measure.modularCharacterFun x : ENNReal) * φ x⁻¹) := by ring
      _ ≤ _ := by gcongr
  · rw [hsupp _ hx]; exact bot_le
end GlobalTheory
