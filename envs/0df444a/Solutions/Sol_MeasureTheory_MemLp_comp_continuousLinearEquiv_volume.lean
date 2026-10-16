-- Prove2me | solution 1 for MeasureTheory.MemLp.comp_continuousLinearEquiv_volume
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:34:17.490483+00:00
-- url     : https://prove2.me/submissions/3923bc34-abc1-4b77-b58f-acc415198a9e

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E ≃L[ℝ] E) (p : ℝ≥0∞) (f : E → ℝ) (hf : MemLp f p volume) :
    MemLp (fun x => f (e x)) p volume := by
  have hd : LinearMap.det e.toLinearEquiv.toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hf' : MemLp f p (Measure.map e volume) := by
    rw [hm]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hf'.comp_of_map e.continuous.aemeasurable
