-- Prove2me | solution 2 for Gradient.convex_first_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:54:07.78185+00:00
-- url     : https://prove2.me/submissions/475328a7-369e-476d-8615-529a79ec99e8

import Mathlib
import Theorems.Thm_FullFormalization_convexOn_le_gradient

set_option autoImplicit false
open scoped InnerProductSpace
open scoped RealInnerProductSpace

-- Same first-order condition, phrased with an explicit gradient field `G` instead of Mathlib's
-- `gradient`: a pointwise `HasGradientAt` makes `F` differentiable and pins `gradient F x` to
-- `G x`, so the two statements carry the same content.
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  have hd : Differentiable ℝ F := fun z => (hF z).differentiableAt
  have hg : gradient F x = G x := (hF x).gradient
  have h := FullFormalization.convexOn_le_gradient hc hd x y
  rwa [hg] at h
