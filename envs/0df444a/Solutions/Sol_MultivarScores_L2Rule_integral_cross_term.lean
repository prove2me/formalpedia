-- Prove2me | solution 1 for MultivarScores.L2Rule.integral_cross_term
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:38.65682+00:00
-- url     : https://prove2.me/submissions/245ab75b-31bb-4a7a-8044-bde0e6a9afe2

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

set_option autoImplicit false
open MeasureTheory MultivarScores.L2Rule

theorem solution {d : ℕ} (PY : Measure (E d)) [IsProbabilityMeasure PY]
    (g w h : E d → ℝ) (hg : Measurable g) (hw : Measurable w) (hh : Measurable h)
    (hint : Integrable (fun p : E d × E d => g p.2 * w (p.2 - p.1) * h p.2) (PY.prod volume)) :
    ∫ s, (∫ z, g z * w (z - s) * h z) ∂PY = ∫ z, g z * smooth PY w z * h z := by
  have hswap := integral_integral_swap (μ := PY) (ν := (volume : Measure (E d)))
    (f := fun s z => g z * w (z - s) * h z) hint
  rw [hswap]
  congr 1
  funext z
  unfold smooth
  rw [← integral_const_mul, ← integral_mul_const]
