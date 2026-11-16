-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_rootIff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:08:48.506067+00:00
-- url     : https://prove2.me/submissions/36497de6-350b-413d-b9eb-73ffc36d3773

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_diverges
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_continuousOn
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rightDerivZero
import Theorems.Thm_Kyprianou_Ch01_strictConvex_positiveRoot_iff_derivativeNegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The Cramér adjustment root exists iff the premium drift at zero is negative. -/
theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    ((∃ theta : ℝ, 0 < theta ∧ queueLaplaceExponent rate F theta = 0) ↔
      1 < (rate : ℝ) * mu) := by
  have hc : StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (queueLaplaceExponent rate F) :=
    Kyprianou.Ch01.queueLaplaceExponent_strictConvex
      rate hrate F hpositive hfiniteMean mu hmu hmean
  have hzero := Kyprianou.Ch01.queueLaplaceExponent_zero rate F
  have hlarge := Kyprianou.Ch01.queueLaplaceExponent_diverges
    rate hrate F hpositive hfiniteMean mu hmu hmean
  have hcont := Kyprianou.Ch01.queueLaplaceExponent_continuousOn
    rate hrate F hpositive hfiniteMean mu hmu hmean
  have hd := Kyprianou.Ch01.queueLaplaceExponent_rightDerivZero
    rate hrate F hpositive hfiniteMean mu hmu hmean
  have h := Kyprianou.Ch01.strictConvex_positiveRoot_iff_derivativeNegative
    (queueLaplaceExponent rate F) (1 - (rate : ℝ) * mu)
    hc hzero hcont hlarge hd
  simpa only [sub_lt_zero] using h
