-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_exponent_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:05:47.341514+00:00
-- url     : https://prove2.me/submissions/39c57837-d48d-4e28-9a13-1d9760655f44

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Theorems.Thm_LevyFoundations_leanlevy_chat16_compensated_integral_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution (T : LevyFoundations.LevyKhintchineTriple) :
    Continuous (LevyFoundations.exponent T) := by
  unfold LevyFoundations.exponent
  have hInt :=
    LevyFoundations.leanlevy_chat16_compensated_integral_continuous T.levyMeasure_condition
  fun_prop
