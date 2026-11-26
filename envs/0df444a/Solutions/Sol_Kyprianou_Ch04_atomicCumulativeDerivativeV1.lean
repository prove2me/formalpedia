-- Prove2me | solution 1 for Kyprianou.Ch04.atomicCumulativeDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:34:49.340845+00:00
-- url     : https://prove2.me/submissions/ff7b7bbf-a305-438e-a8b3-73c893fee683

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_atomicMeasureMassV1
import Theorems.Thm_Kyprianou_Ch04_atomicMeasureSingularV1
import Theorems.Thm_Kyprianou_Ch04_singularCumulativeDerivativeV1
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- Cumulative mass of a summable atomic family has zero derivative almost everywhere. -/
theorem solution {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) (hn : ∀ i, 0 ≤ w i) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt
      (fun t => ∑' i, (a ⁻¹' Iic t).indicator w i) 0 x := by
  let μ := Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (a i)
  have hmass (S : Set ℝ) (hS : MeasurableSet S) :=
    Kyprianou.Ch04.atomicMeasureMassV1 a w hw hn S hS
  haveI : IsFiniteMeasure μ := ⟨by
    change (Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))) univ < ⊤
    rw [hmass univ MeasurableSet.univ]
    exact ENNReal.ofReal_lt_top⟩
  have hsing : μ.MutuallySingular volume :=
    Kyprianou.Ch04.atomicMeasureSingularV1 a w hw
  have he : (fun t : ℝ => (μ (Iic t)).toReal) =
      fun t => ∑' i, (a ⁻¹' Iic t).indicator w i := by
    funext t
    change ((Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))) (Iic t)).toReal = _
    rw [hmass (Iic t) measurableSet_Iic, ENNReal.toReal_ofReal]
    exact tsum_nonneg fun i => indicator_nonneg (fun _ _ => hn i) i
  simpa only [he] using Kyprianou.Ch04.singularCumulativeDerivativeV1 μ hsing
