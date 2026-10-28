-- Prove2me | solution 1 for MonotoneOn.of_hasDerivAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T16:29:42.806529+00:00
-- url     : https://prove2.me/submissions/33010387-716d-408c-9feb-a773345f987f

import Mathlib

-- carved verbatim out of submission 108d25ac-4cbb-466b-9bd4-122188ee844b, lines 83-93

section
open Set

theorem solution {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

end
