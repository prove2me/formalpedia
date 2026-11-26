-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BinaryCadlagFlatV15
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:17:13.546807+00:00
-- url     : https://prove2.me/submissions/89da117c-9c69-4e5e-810b-9d7c7badfb99

import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagNoJumpContinuousV17
import Theorems.Thm_Kyprianou_Ch04_exercise41BinaryContinuousFlatV17
import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (f : NNReal → ℝ)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (s t : NNReal) (hst : s ≤ t)
    (hJump : ∀ u ∈ Ioc s t, f u - Function.leftLim f u = 0) :
    f s = f t := by
  exact exercise41BinaryContinuousFlatV17 f hVal s t hst
    (exercise41CadlagNoJumpContinuousV17 f hR hL s t hJump)