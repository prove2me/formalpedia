-- Prove2me | solution 2 for Gradient.hasDerivAt_line_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:21:48.19599+00:00
-- url     : https://prove2.me/submissions/5232d7d5-f8e7-4579-b43c-0dc070e28b2b

import Mathlib
import Theorems.Thm_Gradient_hasDerivAt_line

set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace

-- the same fact as Gradient.hasDerivAt_line, in the phrasing that takes `gradient h` as a function:
-- `Differentiable ℝ h` supplies `HasGradientAt h (gradient h x) x` at every point.
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t :=
  Gradient.hasDerivAt_line (fun z => (hd z).hasGradientAt) x v t
