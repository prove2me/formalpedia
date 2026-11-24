-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.continuation_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:12.80359+00:00
-- url     : https://prove2.me/submissions/2bb9c59d-4ec7-4bfe-ab6c-f06d31431487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_differentiableAt_mel
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_mel_le
import Theorems.Thm_GlobalTheory_Hk_RayCont_sum_norm_isBigO
import Theorems.Thm_GlobalTheory_Hk_RayCont_LSeries_eq
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_res_le
import Theorems.Thm_GlobalTheory_Hk_RayCont_conj_res
import Theorems.Thm_GlobalTheory_Hk_RayCont_mel_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  intro 𝓕 χ
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩, fun s hs => ?_, fun h s => ?_⟩
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
      (isOpen_lt continuous_const continuous_re)
    have hm := differentiableAt_mel 𝓕 χ hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold LFam.F
    split_ifs <;> fun_prop
  · exact LSeriesSummable_of_sum_norm_bigO (sum_norm_isBigO 𝓕 χ) zero_le_one hs
  · have hs1 : s - 1 ≠ 0 := fun h => by
      rw [sub_eq_zero.1 h] at hs
      simp at hs
    rw [LSeries_eq 𝓕 χ hs, LFam.F]
    split_ifs with h
    · field_simp
      ring
    · simp [LFam.res, h]
  · have hB := 𝓕.B_ge
    have hm : ‖𝓕.mel χ s‖ ≤ 200 * 𝓕.B := by
      refine (norm_mel_le 𝓕 χ (by linarith)).trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hr := norm_res_le 𝓕 χ
    have h0 := norm_nonneg s
    have h1 : ‖s * 𝓕.mel χ s‖ ≤ ‖s‖ * (200 * 𝓕.B) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hm h0
    have hBs : 0 ≤ 𝓕.B * ‖s‖ := by positivity
    have hBs2 : 0 ≤ 𝓕.B * ‖s‖ ^ 2 := by positivity
    rw [LFam.F]
    split_ifs
    · have h2 : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
      have h3 : ‖(s - 1) * s * 𝓕.mel χ s‖ ≤ (‖s‖ + 1) * (‖s‖ * (200 * 𝓕.B)) := by
        rw [mul_assoc, norm_mul]
        exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      have h4 : ‖𝓕.res χ * s‖ ≤ 4 * 𝓕.B * ‖s‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hr h0
      refine (norm_add_le _ _).trans ?_
      nlinarith
    · nlinarith
  · rw [LFam.F, LFam.F, mel_conj 𝓕 χ h]
    split_ifs <;> simp [conj_res]
end GlobalTheory.Hk.RayCont
