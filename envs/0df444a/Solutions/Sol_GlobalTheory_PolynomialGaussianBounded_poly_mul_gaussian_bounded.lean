-- Prove2me | solution 1 for GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:05.330486+00:00
-- url     : https://prove2.me/submissions/cafb3fb0-69a4-4b37-8666-c2e00bc9a88d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialGaussianBounded
namespace GlobalTheory.PolynomialGaussianBounded
theorem _root_.solution :
    ∀ (c : ℝ), (0 : ℝ) < c → ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r →
      ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : ((1 : ℝ) + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    calc ((1 : ℝ) + r) ^ N ≤ (Real.exp r) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp ((N : ℝ) * r) := by rw [← Real.exp_nat_mul]
  calc ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ)))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ (2 : ℕ))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * c * r - N)]
end GlobalTheory.PolynomialGaussianBounded
