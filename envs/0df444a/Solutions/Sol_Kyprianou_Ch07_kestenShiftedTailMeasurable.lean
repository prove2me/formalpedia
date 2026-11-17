-- Prove2me | solution 1 for Kyprianou.Ch07.kestenShiftedTailMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:07:16.415215+00:00
-- url     : https://prove2.me/submissions/2becba74-bbb5-4075-be4a-3a0b5cc2f0b0

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false



theorem Kyprianou.Ch07.kestenShiftedTailMeasurable
    (G : Measure Real) (x : Real) :
    Measurable (fun a : Real => G (Set.Ioi (x - a))) := by
  apply Monotone.measurable
  intro a b hab
  apply measure_mono
  intro y hy
  simp only [Set.mem_Ioi] at hy ⊢
  linarith

theorem solution
    (G : Measure Real) (x : Real) :
    Measurable (fun a : Real => G (Set.Ioi (x - a))) := by
  first
  | exact Kyprianou.Ch07.kestenShiftedTailMeasurable
  | exact Kyprianou.Ch07.kestenShiftedTailMeasurable ..
  | (apply Kyprianou.Ch07.kestenShiftedTailMeasurable <;> assumption)
