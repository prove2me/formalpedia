-- Prove2me | solution 1 for Kyprianou.Ch04.spatialQuadraticJumpRemainderV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:57.186478+00:00
-- url     : https://prove2.me/submissions/17b9ee0e-91cf-44f7-a33d-365614d55be3

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_Kyprianou_Ch04_boundedSecondDerivativeLipschitzV1
import Theorems.Thm_Kyprianou_Ch04_subtractLinearHasDerivV1
import Theorems.Thm_Kyprianou_Ch04_spatialRemainderFromDerivativeBudgetV1
set_option autoImplicit false

/-- Assemble the quadratic Taylor estimate from its analytic components. -/
theorem solution (f : ℝ → ℝ) (K x z : ℝ)
    (h : ContDiff ℝ 2 f) (hK : 0 ≤ K)
    (hbound : ∀ u, |deriv (deriv f) u| ≤ K) :
    |f (x + z) - f x - z * deriv f x| ≤ K * z ^ 2 := by
  exact Kyprianou.Ch04.spatialRemainderFromDerivativeBudgetV1 f K x z hK
    (fun u => Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1 f K x u h hbound)
    (fun u => Kyprianou.Ch04.subtractLinearHasDerivV1 f x u (h.differentiable (by norm_num)))
