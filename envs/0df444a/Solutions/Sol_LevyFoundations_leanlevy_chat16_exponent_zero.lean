-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_exponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:43:02.426308+00:00
-- url     : https://prove2.me/submissions/7fa51de4-2556-4dc8-a189-88148baddf2b

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_compensatedIntegrand

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution (T : LevyFoundations.LevyKhintchineTriple) :
    LevyFoundations.exponent T 0 = 0 := by
  simp [LevyFoundations.exponent, LevyFoundations.compensatedIntegrand]
