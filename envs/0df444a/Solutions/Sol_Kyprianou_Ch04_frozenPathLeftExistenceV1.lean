-- Prove2me | solution 1 for Kyprianou.Ch04.frozenPathLeftExistenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:16:26.401307+00:00
-- url     : https://prove2.me/submissions/9722669a-928b-421c-8fd8-7aa2e9e71b9f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitAfterV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The frozen path has a finite strict left limit at every positive time. -/
theorem solution (Y L : NNReal → ℝ) (T : NNReal)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u : NNReal, 0 < u →
      ∃ l : ℝ, Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 l) := by
  intro u hu
  by_cases h : u ≤ T
  · exact ⟨L u, Kyprianou.Ch04.frozenPathLeftLimitV1 Y T u (L u) h (hL u hu)⟩
  · exact ⟨Y T, Kyprianou.Ch04.frozenPathLeftLimitAfterV1 Y T u (lt_of_not_ge h)⟩
