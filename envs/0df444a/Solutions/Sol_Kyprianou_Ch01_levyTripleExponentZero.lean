-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripleExponentZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:50:44.367303+00:00
-- url     : https://prove2.me/submissions/0e5aa799-ad4b-4732-8644-8c81def24cae

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_zero_left
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    Kyprianou.Ch01.levyTripleExponent T 0 = 0 := by
  simp [Kyprianou.Ch01.levyTripleExponent,
    ProbabilityTheory.levyCompensatedIntegrand_zero_left]
