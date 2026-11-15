-- Prove2me | solution 1 for Kyprianou.Ch01.gammaLevyMeasure_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:11:14.922212+00:00
-- url     : https://prove2.me/submissions/888acda1-1d28-4517-991d-20d8828e69a9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution (alpha beta : ℝ) :
    gammaLevyMeasure alpha beta {0} = 0 := by
  unfold gammaLevyMeasure
  simp
