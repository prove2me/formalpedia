-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripleExponent_eq_leanLevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:56:41.73128+00:00
-- url     : https://prove2.me/submissions/7d904a07-f531-46f2-9a09-9cde7698120b

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ) :
    Kyprianou.Ch01.levyTripleExponent T xi = T.exponent xi := by
  rw [ProbabilityTheory.LevyKhintchineTriple.exponent_def]
  unfold Kyprianou.Ch01.levyTripleExponent
  push_cast
  ring