-- Prove2me | solution 1 for GlobalTheory.chebyshev_coefficient_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:15.867803+00:00
-- url     : https://prove2.me/submissions/2d5411ea-c2a4-4b64-aec0-b38f4ab8e1f7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Theorems.Thm_GlobalTheory_sum_div_sub_le_two_log_of_partial_sums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.SizeSumC := by
  intro hψ
  refine ⟨806, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hNdef
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hA := sum_div_sub_le_two_log_of_partial_sums (fun n => (Λ n : ℝ)) h N
  have hB : (∑ n ∈ Icc 1 N, (Λ n : ℝ)) / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ h1]; linarith [h N]
  have hz1 : 1 ≤ x ^ (400 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2' := Real.log_two_gt_d9
  have hC : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + 400 * Real.log x := by
    have : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x ^ (400 : ℝ)) :=
      Real.log_le_log h1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hx0] at this
    exact this
  have hD : ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) ≤ 806 * Real.log x := by
    linarith
  calc ∑ n ∈ Icc 1 N, Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ Icc 1 N, x * ((Λ n : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        calc (Λ n : ℝ) * min 1 (x / (n : ℝ)) ≤ (Λ n : ℝ) * (x / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
          _ = x * ((Λ n : ℝ) / (n : ℝ)) := by ring
    _ = x * ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x * (806 * Real.log x) := mul_le_mul_of_nonneg_left hD hx0.le
    _ = 806 * x * Real.log x := by ring
end GlobalTheory
