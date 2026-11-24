-- Prove2me | solution 1 for GlobalTheory.mertens_first_vonMangoldt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:41.246244+00:00
-- url     : https://prove2.me/submissions/e9a64aad-b5da-4434-88cb-8bddd435746c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LogFactorialEqSumVonMangoldtMulDiv
import Theorems.Thm_GlobalTheory_sum_vonMangoldt_div_nat_bounds

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
theorem _root_.solution :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 + 4, by positivity, fun y hy => ?_⟩
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hN' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN
  have hI : Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  obtain ⟨h1, h2⟩ := sum_vonMangoldt_div_nat_bounds _ hN
  have h5 : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h6 : Real.log y ≤ Real.log 4 + Real.log ⌊y⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    have := Nat.lt_floor_add_one y
    linarith
  rw [hI, abs_le]
  constructor <;> linarith
end GlobalTheory
