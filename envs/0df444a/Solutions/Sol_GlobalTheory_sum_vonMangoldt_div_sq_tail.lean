-- Prove2me | solution 1 for GlobalTheory.sum_vonMangoldt_div_sq_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:11.562965+00:00
-- url     : https://prove2.me/submissions/dbd5d6f8-5106-4861-b700-d5a60e4ab351

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Theorems.Thm_GlobalTheory_sum_von_mangoldt_div_sq_tail

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
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ 4 / M := by
  rcases le_or_gt M N with hN | hN
  · have h := sum_von_mangoldt_div_sq_tail hψ M hM N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h2 : (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 ≤ 4 / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      nlinarith [hψ N, mul_le_mul_of_nonneg_right (hψ N) hN0.le]
    linarith
  · rw [Ioc_eq_empty (by omega)]
    simp only [sum_empty]
    positivity
end GlobalTheory
