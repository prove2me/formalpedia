-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_le_of_strict_crossingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:25:57.772049+00:00
-- url     : https://prove2.me/submissions/9a5359a9-952a-489e-8fcf-944a3c322005

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_iff_approachingCrossings
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) (hCross : s < X t ω) :
    firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) := by
  apply (firstUpperPassage_le_iff_approachingCrossings X s ω t).2
  intro ε hε
  exact ⟨t, ht, lt_add_of_pos_right t hε, hCross⟩
