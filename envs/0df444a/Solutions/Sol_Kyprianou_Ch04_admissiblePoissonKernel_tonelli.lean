-- Prove2me | solution 1 for Kyprianou.Ch04.admissiblePoissonKernel_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:20:49.328142+00:00
-- url     : https://prove2.me/submissions/084c8785-fe8e-4952-a299-0b65a07e1a3e

import Mathlib
import Theorems.Thm_thm_8_3
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (phi : ℝ → ℝ → Ω → ℝ)
    (hPhi : Kyprianou.Ch04.IsAdmissiblePoissonKernel P F phi)
    (t : ℝ≥0) :
    (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (phi (t : ℝ) x ω) ∂ν ∂P) =
    (∫⁻ x, ∫⁻ ω, ENNReal.ofReal (phi (t : ℝ) x ω) ∂P ∂ν) := by
  have hPair : Measurable (fun z : Ω × ℝ =>
      (((t : ℝ), z.2), z.1)) := by fun_prop
  have hMeasReal : Measurable (fun z : Ω × ℝ =>
      phi (t : ℝ) z.2 z.1) := (hPhi.2.1).comp hPair
  have hMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (phi (t : ℝ) z.2 z.1)) :=
    ENNReal.measurable_ofReal.comp hMeasReal
  exact (thm_8_3 P ν hMeas).1
