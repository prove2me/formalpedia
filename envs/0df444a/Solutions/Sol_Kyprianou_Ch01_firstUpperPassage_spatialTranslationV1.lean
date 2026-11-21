-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_spatialTranslationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:32:56.463865+00:00
-- url     : https://prove2.me/submissions/ab7d9596-85f5-44bd-b362-3bc9f2baaada

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s c : ℝ) (ω : Ω) :
    firstUpperPassage (fun t ω => X t ω + c) (s + c) ω =
      firstUpperPassage X s ω := by
  classical
  unfold firstUpperPassage
  simp only [add_lt_add_iff_right]
