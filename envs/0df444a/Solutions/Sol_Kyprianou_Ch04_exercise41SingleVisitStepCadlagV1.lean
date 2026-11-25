-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SingleVisitStepCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:42:11.079398+00:00
-- url     : https://prove2.me/submissions/34410fbb-054a-41b2-be99-7c900127a86c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepRightContinuousV1
import Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepLeftLimitV1

open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution (s : NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0) (Ici t) t) ∧
    (∀ t : NNReal, 0 < t →
      ∃ l : ℝ, Tendsto
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0)
        (nhdsWithin t (Iio t)) (nhds l)) := by
  exact ⟨Kyprianou.Ch04.exercise41SingleVisitStepRightContinuousV1 s,
    Kyprianou.Ch04.exercise41SingleVisitStepLeftLimitV1 s⟩
