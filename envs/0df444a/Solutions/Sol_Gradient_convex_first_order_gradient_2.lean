-- Prove2me | solution 2 for Gradient.convex_first_order_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:21:47.416376+00:00
-- url     : https://prove2.me/submissions/3bcc9ff3-671c-4c43-8d67-c7964a92e9a8

import Mathlib
import Theorems.Thm_Gradient_convex_first_order

set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace

-- the same fact as Gradient.convex_first_order, in the phrasing that takes `gradient h` as a function:
-- `Differentiable ℝ h` supplies `HasGradientAt h (gradient h x) x` at every point.
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h) (x y : H) :
    h x + ⟪gradient h x, y - x⟫_ℝ ≤ h y :=
  Gradient.convex_first_order (fun z => (hd z).hasGradientAt) hc x y
