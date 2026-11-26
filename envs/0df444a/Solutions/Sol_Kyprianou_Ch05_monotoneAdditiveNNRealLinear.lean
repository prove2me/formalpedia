-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneAdditiveNNRealLinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:15:47.299803+00:00
-- url     : https://prove2.me/submissions/95556298-2fd3-4f3b-bfe0-0a69e32bda06

import Mathlib
import Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
open scoped NNReal
set_option autoImplicit false

/-- Transfer the proved nonnegative additive linearity theorem to NNReal. -/
theorem solution (f : NNReal → Real) (hadd : ∀ s t, f (s+t) = f s + f t)
    (hm : Monotone f) : ∀ t : NNReal, f t = (t : Real) * f 1 := by
  have hz : f 0 = 0 := by
    have h := hadd 0 0
    simp at h
    linarith
  let g : Real → Real := fun x => f x.toNNReal
  have ha (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      g (s+t) = g s + g t := by
    change f (s+t).toNNReal = f s.toNNReal + f t.toNNReal
    rw [Real.toNNReal_add hs ht, hadd]
  have hn (s : Real) (_hs : 0 ≤ s) : 0 ≤ g s := by
    rw [← hz]
    exact hm (show (0 : NNReal) ≤ s.toNNReal from bot_le)
  intro t
  have h := APFPaper5.K1.additive_nonneg_linear g ha hn (t : Real) t.coe_nonneg
  simpa [g] using h
