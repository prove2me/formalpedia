-- Prove2me | solution 1 for GlobalTheory.sum_div_sub_le_two_log_of_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:12.223655+00:00
-- url     : https://prove2.me/submissions/4b84ca75-24d0-4108-8de1-2b7a6187c6cf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums

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
theorem _root_.solution (a : ℕ → ℝ)
    (h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ≤ 2 * (N : ℝ)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℝ) - (∑ n ∈ Icc 1 N, a n) / ((N : ℝ) + 1)
      ≤ 2 * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := h (N + 1)
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)] at hN
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast at hN ⊢
    set P := ∑ n ∈ Icc 1 N, a n
    set S := ∑ n ∈ Icc 1 N, a n / (n : ℝ)
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by linarith
    have hlog : 1 / ((N : ℝ) + 1 + 1) ≤ Real.log ((N : ℝ) + 1 + 1) - Real.log ((N : ℝ) + 1) := by
      have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
      rw [Real.log_div h1.ne' h2.ne'] at this
      have e : ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1) - 1 = -(1 / ((N : ℝ) + 1 + 1)) := by
        field_simp; ring
      linarith
    have e : S + a (N + 1) / ((N : ℝ) + 1) - (P + a (N + 1)) / ((N : ℝ) + 1 + 1)
        = (S - P / ((N : ℝ) + 1)) + ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1)) := by
      field_simp; ring
    have h3 : (P + a (N + 1)) / ((N : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ h1]; linarith
    have h4 : ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1))
        ≤ 2 * (1 / ((N : ℝ) + 1 + 1)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    rw [e]
    linarith
end GlobalTheory
