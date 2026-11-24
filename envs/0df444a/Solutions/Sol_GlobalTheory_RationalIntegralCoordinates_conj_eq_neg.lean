-- Prove2me | solution 1 for GlobalTheory.RationalIntegralCoordinates.conj_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:46.414952+00:00
-- url     : https://prove2.me/submissions/a62c7b78-4675-45fd-8efe-de5db0a9a117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalIntegralCoordinates
namespace GlobalTheory.RationalIntegralCoordinates
theorem _root_.solution {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : r.re = 0 := by
    by_contra hne
    have him : r.im = 0 := by
      have hprod : r.re * r.im = 0 := by linarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hne
      · exact h
    rw [him] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [hre]
end GlobalTheory.RationalIntegralCoordinates
