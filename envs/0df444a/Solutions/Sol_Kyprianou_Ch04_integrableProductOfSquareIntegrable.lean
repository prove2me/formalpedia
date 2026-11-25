-- Prove2me | solution 1 for Kyprianou.Ch04.integrableProductOfSquareIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:22:51.434177+00:00
-- url     : https://prove2.me/submissions/d0e7e8b4-462f-4701-bf14-83679fcb9fe7

import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory
set_option autoImplicit false
universe u

/-- Square-integrability of real-valued functions implies integrability of their product. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hXm : AEStronglyMeasurable X P)
    (hYm : AEStronglyMeasurable Y P)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P) :
    Integrable (fun ω => X ω * Y ω) P := by
  have hX : MemLp X 2 P := (memLp_two_iff_integrable_sq hXm).2 hX2
  have hY : MemLp Y 2 P := (memLp_two_iff_integrable_sq hYm).2 hY2
  have h := hX.integrable_mul hY
  convert h using 1
  funext ω
  simp only [Pi.mul_apply]
