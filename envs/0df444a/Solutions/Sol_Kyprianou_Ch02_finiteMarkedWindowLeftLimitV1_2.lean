-- Prove2me | solution 2 for Kyprianou.Ch02.finiteMarkedWindowLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:06:31.346308+00:00
-- url     : https://prove2.me/submissions/ff86cdb5-99ec-4d72-b2dd-20a9066010d6

import Theorems.Thm_Kyprianou_Ch02_markedIntegralLeftLimitFromFiniteWindowV1
import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfinite : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤) :
    Tendsto (fun s : ℝ≥0 => ∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ)) := by
  exact Kyprianou.Ch02.markedIntegralLeftLimitFromFiniteWindowV1 μ B hB hsmall T t htT hfinite
