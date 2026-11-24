-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_scale_negative_argument_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:17:00.477272+00:00
-- url     : https://prove2.me/submissions/977dd487-5403-460c-94ff-38dddfa3ef20

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
/-- Negative-argument zero extension at every nonnegative discount. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0 := by
  intro ψ W hW z hz q hq
  rcases hW q hq with ⟨_, hnegzero, _, _, _, _⟩
  exact hnegzero z hz

