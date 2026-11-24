-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.continuousOn_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:42.064506+00:00
-- url     : https://prove2.me/submissions/cbb3f7f1-8943-4eb9-be30-12259e747e90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_weight_bound

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
theorem _root_.solution {ι : Type} {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} (hc : Continuous wt)
    {α β : ℝ} (hs : ∀ y, wt y ≠ 0 → α ≤ y ∧ y ≤ β) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-2 : ℝ)) :
    ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := weight_bound hc hs
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  have hcont : ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi (t0 / 2)) := by
    refine continuousOn_tsum (u := fun i => ‖a i‖ * N i ^ (-2 : ℝ) * (M * (t0 / 2) ^ (-2 : ℝ)))
      (fun i => (continuous_const.mul (hc.comp (continuous_id.mul continuous_const))).continuousOn)
      (hsum.mul_right _) ?_
    intro i t ht
    have ht' : t0 / 2 < t := ht
    by_cases hai : a i = 0
    · simp [hai]
    have hNi : (1 : ℝ) ≤ N i := hN i hai
    have htN : 0 < t * N i := mul_pos (by linarith) (by linarith)
    rw [norm_mul]
    have h1 := hM (t * N i) htN
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : t ^ (-2 : ℝ) ≤ (t0 / 2) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) ht'.le (by norm_num)
    have hNn : 0 ≤ N i ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc ‖a i‖ * ‖wt (t * N i)‖ ≤ ‖a i‖ * (M * (t ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖a i‖ * (M * ((t0 / 2) ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 hNn) hM0) (norm_nonneg _)
      _ = _ := by ring
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt
end GlobalTheory.SmoothedSumMellin
