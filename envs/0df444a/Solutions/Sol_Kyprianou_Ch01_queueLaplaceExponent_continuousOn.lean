-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:08:58.138855+00:00
-- url     : https://prove2.me/submissions/03c3bedd-5f66-4bf9-8ee5-c0f93c962125

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rightDerivZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    ContinuousOn (queueLaplaceExponent rate F) (Set.Ici (0 : ℝ)) := by
  have hc := Kyprianou.Ch01.queueLaplaceExponent_strictConvex
    rate hrate F hpositive hfiniteMean mu hmu hmean
  have hd := Kyprianou.Ch01.queueLaplaceExponent_rightDerivZero
    rate hrate F hpositive hfiniteMean mu hmu hmean
  exact hc.convexOn.continuousOn_Ici hd.continuousWithinAt
