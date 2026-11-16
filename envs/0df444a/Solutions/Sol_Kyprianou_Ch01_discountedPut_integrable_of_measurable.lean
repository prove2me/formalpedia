-- Prove2me | solution 1 for Kyprianou.Ch01.discountedPut_integrable_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:03:56.404877+00:00
-- url     : https://prove2.me/submissions/df8ae52d-42bc-481e-86d4-ea749e38dd10

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_discountedPut_pointwiseBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Bounded measurable discounted payoffs are integrable under a probability measure. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (x K q : ℝ)
    (hK : 0 < K) (hq : 0 < q)
    (tau : Ω → WithTop ℝ≥0)
    (hMeas : Measurable (discountedPut X x K q tau)) :
    Integrable (discountedPut X x K q tau) P := by
  apply Integrable.of_bound hMeas.aestronglyMeasurable K
  filter_upwards [] with omega
  have hb := Kyprianou.Ch01.discountedPut_pointwiseBound
    X x K q hK hq tau omega
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2
