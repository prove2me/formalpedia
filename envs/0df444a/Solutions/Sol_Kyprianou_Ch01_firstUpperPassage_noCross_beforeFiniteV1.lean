-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_noCross_beforeFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:59:13.810646+00:00
-- url     : https://prove2.me/submissions/2ca7389e-b3cf-4a77-8cee-ddc4906c243c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_of_strict_crossingV1
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω)
    (hInitial : X 0 ω ≤ s) (τ : ℝ≥0)
    (hPass : firstUpperPassage X s ω = (τ : WithTop ℝ≥0)) :
    ∀ t : ℝ≥0, t < τ → X t ω ≤ s := by
  intro t ht
  by_contra hNot
  have hCross : s < X t ω := lt_of_not_ge hNot
  by_cases hz : t = 0
  · subst t
    exact (not_lt_of_ge hInitial) hCross
  · have htPos : 0 < t := pos_of_ne_zero hz
    have hBound :=
      firstUpperPassage_le_of_strict_crossingV1 X s ω t htPos hCross
    rw [hPass] at hBound
    have hLe : τ ≤ t := WithTop.coe_le_coe.mp hBound
    exact (not_le_of_gt ht) hLe
