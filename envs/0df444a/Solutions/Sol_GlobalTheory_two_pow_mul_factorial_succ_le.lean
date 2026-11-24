-- Prove2me | solution 1 for GlobalTheory.two_pow_mul_factorial_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:51.402639+00:00
-- url     : https://prove2.me/submissions/5963cf43-7372-4adf-875b-5a93314ce1f4

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
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 2 * ((n : ℝ) + 1) ^ (n + 1) ≤ ((n : ℝ) + 1 + 1) ^ (n + 1) := by
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have h := one_add_mul_le_pow (a := ((n : ℝ) + 1)⁻¹) (by have := inv_pos.mpr hpos; linarith)
        (n + 1)
      have h1 : ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ = 1 := by push_cast; field_simp
      rw [h1] at h
      have h2 : ((n : ℝ) + 1 + 1) = (1 + ((n : ℝ) + 1)⁻¹) * (n + 1) := by field_simp
      rw [h2, mul_pow]
      gcongr
      linarith
    rw [Nat.factorial_succ (n + 1), pow_succ 2 n, pow_succ _ (n + 1)]
    push_cast
    have : (0 : ℝ) ≤ n + 1 + 1 := by positivity
    calc _ = (2 * (2 ^ n * ((n + 1).factorial : ℝ))) * ((n : ℝ) + 1 + 1) := by ring
      _ ≤ (2 * ((n : ℝ) + 1) ^ (n + 1)) * ((n : ℝ) + 1 + 1) := by gcongr
      _ ≤ _ := by gcongr
end GlobalTheory
