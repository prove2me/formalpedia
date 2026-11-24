-- Prove2me | solution 1 for GlobalTheory.sum_von_mangoldt_div_sq_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:12.109181+00:00
-- url     : https://prove2.me/submissions/b9d8de1f-062a-4b61-a4d0-7b3319dc1639

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail

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
theorem _root_.solution
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 + 4 / M - 4 / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (by positivity)
    simpa using this
  | succ N hN ih =>
    rw [sum_Ioc_succ_top hN, sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hA := hψ N
    set A := ∑ n ∈ Icc 1 N, Λ n
    push_cast
    have h1 : 0 ≤ 1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_right hA h1
    have h3 : 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) ≤ 4 / N - 4 / ((N : ℝ) + 1) := by
      have e : 4 / N - 4 / ((N : ℝ) + 1) - 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2)
          = 2 / (N * ((N : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      have : 0 ≤ 2 / (N * ((N : ℝ) + 1) ^ 2) := by positivity
      linarith
    have e1 : A * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) = A / (N : ℝ) ^ 2 - A / ((N : ℝ) + 1) ^ 2 := by
      ring
    rw [add_div]
    linarith
end GlobalTheory
