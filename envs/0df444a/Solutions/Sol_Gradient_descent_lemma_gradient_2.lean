-- Prove2me | solution 2 for Gradient.descent_lemma_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:21:46.763998+00:00
-- url     : https://prove2.me/submissions/378469b6-5fa4-4227-a5c8-c7ef842fc4b8

import Mathlib
import Theorems.Thm_Gradient_descent_lemma

set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace

-- the same fact as Gradient.descent_lemma, in the phrasing that takes `gradient h` as a function:
-- `Differentiable ℝ h` supplies `HasGradientAt h (gradient h x) x` at every point.
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : H) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 :=
  Gradient.descent_lemma (fun z => (hd z).hasGradientAt) hL x y
