-- Prove2me | solution 1 for Kyprianou.Ch04.finiteKernelMarkedPushforwardMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:33.390743+00:00
-- url     : https://prove2.me/submissions/50cc6046-2060-4fa7-b146-c32b2e763be8

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (κ : ProbabilityTheory.Kernel Omega (Real × Real))
    (hκ : ∀ w, IsFiniteMeasure (κ w)) :
    Measurable (fun w => Measure.map
      (fun z : Real × Real => ((z.1.toNNReal, w), z.2)) (κ w)) := by
  let J : Omega × (Real × Real) → ((NNReal × Omega) × Real) :=
    fun z => ((z.2.1.toNNReal, z.1), z.2.2)
  have hJ : Measurable J :=
    ((continuous_real_toNNReal.measurable.comp measurable_snd.fst).prodMk
      measurable_fst).prodMk measurable_snd.snd
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun w => (Measure.map (fun z : Real × Real =>
      ((z.1.toNNReal, w), z.2)) (κ w)) S) =
      fun w => κ w (Prod.mk w ⁻¹' (J ⁻¹' S)) := by
    funext w
    exact Measure.map_apply (hJ.comp measurable_prodMk_left) hS
  rw [he]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite (hJ hS) hκ
