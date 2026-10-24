-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.lintegral_congr_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:28:26.484492+00:00
-- url     : https://prove2.me/submissions/d5cb522e-e47a-47a0-96df-70dcf00856ca

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution (f g : Real → ENNReal)
    (h : ∀ t ∈ Set.Icc (0 : Real) 1, f t = g t) :
    ∫⁻ t in Set.Icc (0 : Real) 1, f t ∂MeasureTheory.volume =
      ∫⁻ t in Set.Icc (0 : Real) 1, g t ∂MeasureTheory.volume := by
  exact MeasureTheory.setLIntegral_congr_fun measurableSet_Icc h