-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanValue_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:04:56.583727+00:00
-- url     : https://prove2.me/submissions/222be7e1-852f-48af-a479-324690e3e5c1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (K barrier phi : ℝ) :
    Measurable (mckeanValue K barrier phi) := by
  classical
  change Measurable
    (fun y : ℝ => if y < barrier then
      K - Real.exp y
    else
      (K - Real.exp barrier) * Real.exp (-phi * (y - barrier)))
  exact Measurable.ite
    (measurableSet_lt measurable_id measurable_const)
    (by fun_prop) (by fun_prop)
