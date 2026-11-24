-- Prove2me | solution 1 for GlobalTheory.sum_zeta_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:12.8104+00:00
-- url     : https://prove2.me/submissions/4a2b00f9-3a75-4a34-a415-655dd61bf02b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : ℕ) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : (N : ℝ) ≤ X) :
    ((∑ n ∈ Ioc 0 N, (ζ ^ (k + 1) : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ N * (1 + Real.log X) ^ k := by
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  induction k generalizing N with
  | zero => simp only [zero_add, pow_one, ArithmeticFunction.sum_Ioc_zeta, pow_zero, mul_one, le_refl]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
    have hH : ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ ≤ 1 + Real.log X := by
      have h1 := harmonic_le_one_add_log N
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
      have h2 : Real.log N ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos N with rfl | h
        · simpa using Real.log_nonneg hX
        · exact Real.log_le_log (by exact_mod_cast h) hN
      have h3 : Ioc 0 N = Icc 1 N := rfl
      rw [h3]; linarith
    calc _ ≤ ∑ n ∈ Ioc 0 N, (N * (1 + Real.log X) ^ k) * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
          refine (ih (N / n) (le_trans (by exact_mod_cast Nat.div_le_self N n) hN)).trans ?_
          have : ((N / n : ℕ) : ℝ) ≤ N * (n : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv]; exact Nat.cast_div_le
          calc _ ≤ (N * (n : ℝ)⁻¹) * (1 + Real.log X) ^ k := by gcongr
            _ = _ := by ring
      _ ≤ (N * (1 + Real.log X) ^ k) * (1 + Real.log X) := by
          rw [← mul_sum]; gcongr
      _ = _ := by ring
end GlobalTheory
