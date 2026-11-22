-- Prove2me | solution 1 for LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverageLimit
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:42.356798+00:00
-- url     : https://prove2.me/submissions/1e4dc217-fc39-4162-9950-03a00c915d85

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-! ### Lebesgue differentiation along the left windows -/

/-! ### The modification -/



theorem _root_.solution (hbm : Measurable (Function.uncurry b)) (T : ℝ) :
    Measurable (Function.uncurry (leftAverageLimit b T)) := by
  have hm (i : ℕ) : Measurable (Function.uncurry (leftAverage b (1 / ((i : ℝ) + 1)))) :=
    measurable_uncurry_leftAverage hbm _
  have hl : Measurable (fun p : Ω × ℝ =>
      Filter.limsup (fun i : ℕ => leftAverage b (1 / ((i : ℝ) + 1)) p.1 p.2) Filter.atTop) := by
    first | exact Measurable.limsup hm | exact measurable_limsup hm | exact?
  have hg := hl.indicator (measurable_snd measurableSet_Icc :
    MeasurableSet (Prod.snd ⁻¹' Set.Icc (0 : ℝ) T : Set (Ω × ℝ)))
  convert hg using 1
  funext p
  by_cases hq : 0 ≤ p.2 ∧ p.2 ≤ T <;>
    simp [Function.uncurry, leftAverageLimit, Set.indicator_apply, hq]
