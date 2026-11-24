-- Prove2me | solution 1 for GlobalTheory.powerSum_second_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:48.395801+00:00
-- url     : https://prove2.me/submissions/a7e1dea0-f15e-4b34-9d1a-317a5e99c5e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficients
import Theorems.Thm_GlobalTheory_PowerSumSecond_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open PowerSumSecond
namespace GlobalTheory
theorem _root_.solution :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  refine ⟨16 * Real.exp 1 ^ 2, ?_, fun N M z i₀ => ?_⟩
  · have : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ (Real.one_le_exp zero_le_one)
    linarith
  have hN : 0 < N := i₀.pos
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  by_cases h0 : z i₁ = 0
  · refine ⟨M + 1, le_rfl, by omega, ?_⟩
    have : ‖z i₀‖ = 0 := le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)
    rw [this, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  have hR : 0 < ‖z i₁‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk, hk'⟩ := Finset.exists_max_image (Finset.Icc (M + 1) (M + N))
    (fun k => ‖∑ i, (z i / z i₁) ^ k‖) ⟨M + 1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  rw [Finset.mem_Icc] at hk
  refine ⟨k, hk.1, hk.2, ?_⟩
  have hc := core N M (fun i => z i / z i₁) i₁ (by simp [h0])
    (fun i => by
      rw [norm_div, div_le_one hR]; exact hi₁ i (Finset.mem_univ _))
    _ (fun j h1 h2 => hk' j (Finset.mem_Icc.2 ⟨h1, h2⟩))
  simp only [div_pow] at hc
  rw [← Finset.sum_div, norm_div, norm_pow, le_div_iff₀ (by positivity), ← div_pow] at hc
  refine le_trans ?_ hc
  gcongr
  exact hi₁ i₀ (Finset.mem_univ _)
end GlobalTheory
