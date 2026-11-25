-- Prove2me | solution 1 for Kyprianou.Ch04.pointwiseFiniteKernelJointLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:10:26.225193+00:00
-- url     : https://prove2.me/submissions/b1b43e1c-bf33-4a89-960b-55975169e51f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

/-- Push the finite random measure forward by the map pairing the sample with each mark. -/
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E)
    (hR : ∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S))
    (hFin : ∀ w, IsFiniteMeasure (R w))
    (f : Omega × E → ENNReal) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ z, f (w,z) ∂(R w)) := by
  let K : ProbabilityTheory.Kernel Omega E :=
    ⟨R, Measure.measurable_of_measurable_coe R hR⟩
  let J (w : Omega) := Measure.map (Prod.mk w) (K w)
  have hJ : Measurable J := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have he (w : Omega) : J w S = K w (Prod.mk w ⁻¹' S) :=
      Measure.map_apply measurable_prodMk_left hS
    simp_rw [he]
    exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite hS hFin
  have h := (Measure.measurable_lintegral hf).comp hJ
  simpa only [Function.comp_def, J, lintegral_map hf measurable_prodMk_left, K, ProbabilityTheory.Kernel.coe_mk] using h
