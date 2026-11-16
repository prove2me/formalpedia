-- Prove2me | solution 1 for Kyprianou.Ch02.oneSubExpLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:00:54.347471+00:00
-- url     : https://prove2.me/submissions/adb11ff6-bd2c-4890-97e8-2fe106a7efd7

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_Kyprianou_Ch02_oneSubExpBoundSmall
import Theorems.Thm_Kyprianou_Ch02_oneSubExpBoundLarge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x) :
    min 1 x ≤ 2 * (1 - Real.exp (-x)) := by
  by_cases hx1 : x ≤ 1
  case pos =>
    have hsmall := Kyprianou.Ch02.oneSubExpBoundSmall x hx hx1
    simpa [min_eq_right hx1] using hsmall
  case neg =>
    have hlarge : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have hstep := Kyprianou.Ch02.oneSubExpBoundLarge x hlarge
    simpa [min_eq_left hlarge] using hstep
