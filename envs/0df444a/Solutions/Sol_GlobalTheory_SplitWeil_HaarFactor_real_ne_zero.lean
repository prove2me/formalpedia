-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.real_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:20:04.204858+00:00
-- url     : https://prove2.me/submissions/20a13c9d-ac27-43b2-ae89-506fc0bafc8e

import Mathlib
open MeasureTheory
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]


theorem solution {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (μ.real (U : Set A) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr ((MeasureTheory.measureReal_ne_zero_iff hUc.measure_lt_top.ne).mpr (hUo.measure_ne_zero μ ⟨0,U.zero_mem⟩))
