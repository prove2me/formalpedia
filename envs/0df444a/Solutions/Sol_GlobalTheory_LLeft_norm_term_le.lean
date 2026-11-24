-- Prove2me | solution 1 for GlobalTheory.LLeft.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:09.587928+00:00
-- url     : https://prove2.me/submissions/0c2feda6-b1cd-4707-a8c0-fbd1ade0b82b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_norm_diffPow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (b : ℕ → ℂ) (K R : ℝ) (hb : ∀ n, ‖b n‖ ≤ K) (s : ℂ)
    (hs : -(15 / 8 : ℝ) ≤ s.re) (hR : ‖s‖ ≤ R) (n : ℕ) :
    ‖b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ K * (R + 3) ^ 3 * ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hb 0)
  have h1 := norm_diffPow_le 3 s ((n : ℝ) + 1) (by positivity) (by push_cast; linarith)
  have h2 : ((n : ℝ) + 1) ^ (-(s.re + (3 : ℕ))) ≤ ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by push_cast; linarith)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  rw [norm_mul, mul_assoc]
  refine mul_le_mul (hb n) (h1.trans ?_) (norm_nonneg _) hK
  refine mul_le_mul ?_ h2 (by positivity) (by positivity)
  push_cast
  gcongr
end GlobalTheory.LLeft
