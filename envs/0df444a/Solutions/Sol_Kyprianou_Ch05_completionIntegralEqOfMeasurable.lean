-- Prove2me | solution 1 for Kyprianou.Ch05.completionIntegralEqOfMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:33.060287+00:00
-- url     : https://prove2.me/submissions/a2ef5ef9-b392-4245-b5b3-48ab582153f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_completionMapEqOfAEMeasurable
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (f : Omega → Real)
    (hf : Measurable (fun w : NullMeasurableSpace Omega P => f w)) :
    (∫ w : NullMeasurableSpace Omega P, f w ∂P.completion) =
      ∫ w : Omega, f w ∂P := by
  have hn : NullMeasurable f P := hf
  have ha := hn.aemeasurable
  have hm := Kyprianou.Ch05.completionMapEqOfAEMeasurable P f ha
  calc
    _ = ∫ z : Real, z ∂(Measure.map
        (fun w : NullMeasurableSpace Omega P => f w) P.completion) :=
      (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ z : Real, z ∂(Measure.map f P) := by rw [hm]
    _ = _ := integral_map ha aestronglyMeasurable_id
