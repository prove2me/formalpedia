-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.exists_bound_LSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:20.891873+00:00
-- url     : https://prove2.me/submissions/abea5d0d-0462-4912-a4fb-bd4e9ed03533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe
import Theorems.Thm_GlobalTheory_Hk_LogDerivHalf_norm_lamChi_le
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_norm_lamChi_le


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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf
namespace GlobalTheory.Hk.LogDerivHalf
theorem _root_.solution : ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 7 / 4 ≤ s.re →
    ‖LSeries (𝓕.lamChi χ) s‖ ≤ K := by
  set s₀ : ℂ := ((7 / 4 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = 7 / 4 := by simp [hs₀]
  have hΛ : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hs₀re]; norm_num)).norm
  refine ⟨2 * ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖,
    mul_nonneg (by norm_num) (tsum_nonneg fun _ => norm_nonneg _), ?_⟩
  intro 𝓕 χ s hs
  have P : ∀ n, ‖LSeries.term (𝓕.lamChi χ) s n‖ ≤ 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := by
    intro n
    calc ‖LSeries.term (𝓕.lamChi χ) s n‖ ≤ ‖LSeries.term (𝓕.lamChi χ) s₀ n‖ :=
          LSeries.norm_term_le_of_re_le_re _ (by rw [hs₀re]; exact hs) n
      _ ≤ ‖LSeries.term (fun n => 2 * (Λ n : ℂ)) s₀ n‖ := by
          refine LSeries.norm_term_le _ ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          simpa using norm_lamChi_le 𝓕 χ n
      _ = 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
          split_ifs
          · simp
          · rw [norm_mul, mul_div_assoc]
            norm_num
  have hS : Summable fun n => ‖LSeries.term (𝓕.lamChi χ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) P (hΛ.mul_left 2)
  calc ‖LSeries (𝓕.lamChi χ) s‖ = ‖∑' n, LSeries.term (𝓕.lamChi χ) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (𝓕.lamChi χ) s n‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' n, 2 * ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := Summable.tsum_le_tsum P hS (hΛ.mul_left 2)
    _ = 2 * ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) s₀ n‖ := tsum_mul_left
end GlobalTheory.Hk.LogDerivHalf
