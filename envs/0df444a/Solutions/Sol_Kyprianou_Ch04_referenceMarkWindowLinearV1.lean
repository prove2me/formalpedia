-- Prove2me | solution 1 for Kyprianou.Ch04.referenceMarkWindowLinearV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:47:53.299869+00:00
-- url     : https://prove2.me/submissions/e9e8e4f9-32f0-4b21-86a6-f0cc299af1a0

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
import Theorems.Thm_Kyprianou_Ch04_physicalMarkIndicatorWindowIntegralV1
open MeasureTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The compensator of a marked window with a time-independent mark kernel is
its clock length times the mark integral. -/
theorem solution (ν : Measure ℝ) [SigmaFinite ν] (t : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B) (Q : ℝ → ℝ) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      B.indicator Q z.2 ∂ referenceIntensity ν) =
      (t : ℝ) * (∫ x in B,Q x ∂ν) := by
  rw [Kyprianou.Ch04.physicalMarkIndicatorWindowIntegralV1
    (referenceIntensity ν) t B hB (fun z => Q z.2)]
  change (∫ z, Q z.2 ∂ (referenceIntensity ν).restrict
    (Icc (0 : ℝ) (t : ℝ) ×ˢ B)) = _
  rw [Kyprianou.Ch04.referenceIntensityClosedWindowProductV1 ν t B hB]
  calc
    _ = ∫ z : ℝ × ℝ, (1 : ℝ) * Q z.2 ∂
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod (ν.restrict B)) := by simp
    _ = (∫ s in Icc (0 : ℝ) (t : ℝ), (fun _ : ℝ => (1 : ℝ)) s ∂volume) *
        (∫ x in B, Q x ∂ν) := integral_prod_mul (fun _ : ℝ => (1 : ℝ)) Q
    _ = _ := by
      simp [measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,ENNReal.toReal_ofReal] <;> ring
