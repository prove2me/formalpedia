-- Prove2me | solution 1 for GlobalTheory.SCV.hasFPowerSeriesAt_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:16.377247+00:00
-- url     : https://prove2.me/submissions/912cae2e-c82e-4946-9b9b-5aec8ee479d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_exists_ball_bound
import Theorems.Thm_GlobalTheory_SCV_norm_iteratedFDeriv_le_factorial
import Theorems.Thm_GlobalTheory_SCV_hasSum_taylorSeries_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) :
    HasFPowerSeriesAt f (fun n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c) c := by
  obtain ⟨R, hR, M, hRU, hM⟩ := exists_ball_bound hU hf hc
  have hsub : closedBall c (R / 2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hρ : 0 < R / 2 / (2 * Real.exp 1) := by positivity
  let ρ : NNReal := ⟨R / 2 / (2 * Real.exp 1), hρ.le⟩
  have hρe : (ρ : ℝ) = R / 2 / (2 * Real.exp 1) := rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ M fun n => ?_
    have h1 := norm_iteratedFDeriv_le_factorial hU hf (half_pos hR) (hsub.trans hRU)
      (fun z hz => hM z (hsub hz)) n
    have hn : (0 : ℝ) < n ! := by positivity
    have h2 : ‖(n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c‖ ≤ M * (2 * Real.exp 1 / (R / 2)) ^ n := by
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
      exact h1
    calc ‖(n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c‖ * (ρ : ℝ) ^ n
        ≤ (M * (2 * Real.exp 1 / (R / 2)) ^ n) * (ρ : ℝ) ^ n := by gcongr
      _ = M := by
        rw [mul_assoc, ← mul_pow, hρe,
          show 2 * Real.exp 1 / (R / 2) * (R / 2 / (2 * Real.exp 1)) = 1 by field_simp]
        simp
  · exact_mod_cast hρ
  · intro y hy
    rw [Metric.eball_coe, mem_ball_zero_iff, hρe, lt_div_iff₀ (by positivity)] at hy
    have hy' : ‖y‖ < R := by nlinarith [norm_nonneg y]
    simpa only [smul_apply]
      using hasSum_taylorSeries_ball (hf.mono hRU) hy'
end GlobalTheory.SCV
