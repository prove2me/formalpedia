-- Prove2me | solution 1 for GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:25.716818+00:00
-- url     : https://prove2.me/submissions/2650de20-8d35-466a-9e46-759aa80acbc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjNegSquareNat
namespace GlobalTheory.ConjNegSquareNat
theorem _root_.solution {z : ℂ} {d : ℕ} (hd : (0 : ℕ) < d)
    (h : z ^ (2 : ℕ) = -(↑d : ℂ)) : (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end GlobalTheory.ConjNegSquareNat
