-- Prove2me | solution 1 for KellyStochasticNetworks.wardrop_objective_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:34.193966+00:00
-- url     : https://prove2.me/submissions/96de6428-9a24-4475-bb38-600bee8decc5

import Mathlib

namespace KellyStochasticNetworks

end KellyStochasticNetworks

open KellyStochasticNetworks
theorem solution (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) :
    ConvexOn ℝ Set.univ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) := by
  have hderiv : deriv (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) = D := by
    funext y
    exact Continuous.deriv_integral D hD 0 y
  have hdiff : Differentiable ℝ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) :=
    fun y => (hD.integral_hasStrictDerivAt 0 y).hasDerivAt.differentiableAt
  exact Monotone.convexOn_univ_of_deriv hdiff (by rw [hderiv]; exact hmono)

