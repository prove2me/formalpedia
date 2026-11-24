-- Prove2me | solution 1 for GlobalTheory.sum_vonMangoldt_div_sq_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:10.862526+00:00
-- url     : https://prove2.me/submissions/e725ed91-3539-40c6-be2e-1ef2e264b734

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Theorems.Thm_GlobalTheory_sum_von_mangoldt_div_sq_Ioc_le

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
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤ 4 / (K : ℝ) := by
  rcases le_total K M with hM | hM
  · have h1 := sum_von_mangoldt_div_sq_Ioc_le h K hK M hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have h2 : (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 ≤ 4 / (M : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hM0]
      have := h M
      nlinarith
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity
end GlobalTheory
