-- Prove2me | solution 1 for GlobalTheory.sum_von_mangoldt_div_sq_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:11.464196+00:00
-- url     : https://prove2.me/submissions/1d1784f6-41e9-4b66-8d04-2f2d0fd7a5de

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe

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
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM : K ≤ M) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 + 4 / (K : ℝ) - 4 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 K, Λ n) / (K : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (sq_nonneg _)
    simp only [Ioc_self, sum_empty]
    linarith
  | succ M hM ih =>
    rw [sum_Ioc_succ_top hM, sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hψ := h M
    set ψ := ∑ n ∈ Icc 1 M, Λ n
    push_cast
    have key : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2 ≤ 4 / (M : ℝ) - 4 / ((M : ℝ) + 1) := by
      have e1 : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2
          = ψ * ((2 * M + 1) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      have e2 : 4 / (M : ℝ) - 4 / ((M : ℝ) + 1)
          = 2 * M * ((2 * M + 2) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul hψ _ (by positivity) (by positivity)
      gcongr
      norm_num
    rw [add_div]
    linarith
end GlobalTheory
