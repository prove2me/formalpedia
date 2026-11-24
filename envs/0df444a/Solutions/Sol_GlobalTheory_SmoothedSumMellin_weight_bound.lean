-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:38.386918+00:00
-- url     : https://prove2.me/submissions/e22bcc75-0631-45b8-adb5-f0ca9acc7e49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin
namespace GlobalTheory.SmoothedSumMellin
theorem _root_.solution {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ}
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → ‖wt y‖ ≤ M * y ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0 * (max b 1) ^ 2, by positivity, fun y hy => ?_⟩
  by_cases h0 : wt y = 0
  · rw [h0, norm_zero]
    positivity
  obtain ⟨hay, hyb⟩ := hs y h0
  have hB : ‖wt y‖ ≤ max C 0 := (hC y ⟨hay, hyb⟩).trans (le_max_left _ _)
  rw [Real.rpow_neg hy.le, Real.rpow_two]
  have hyb' : y ^ 2 ≤ (max b 1) ^ 2 := pow_le_pow_left₀ hy.le (hyb.trans (le_max_left _ _)) 2
  have h1 : 1 ≤ (max b 1) ^ 2 * (y ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith
  calc ‖wt y‖ ≤ max C 0 * 1 := by rw [mul_one]; exact hB
    _ ≤ max C 0 * ((max b 1) ^ 2 * (y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = _ := by ring
end GlobalTheory.SmoothedSumMellin
