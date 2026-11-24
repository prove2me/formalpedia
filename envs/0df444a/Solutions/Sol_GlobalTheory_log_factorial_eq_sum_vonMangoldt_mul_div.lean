-- Prove2me | solution 1 for GlobalTheory.log_factorial_eq_sum_vonMangoldt_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:58.175898+00:00
-- url     : https://prove2.me/submissions/1a6da8b7-fc4c-4edd-abab-0ae876e7b2be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LogFactorialEqSumVonMangoldtMulDiv

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
theorem _root_.solution (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N, vonMangoldt_mul_zeta]
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]
    rfl
end GlobalTheory
