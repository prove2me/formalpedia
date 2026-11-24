-- Prove2me | solution 1 for Kyprianou.Ch03.momentSubmulProductSumIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:31:57.41904+00:00
-- url     : https://prove2.me/submissions/215a75a7-83c5-45f6-82bb-d02f8be4a9b5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hnu : Integrable g nu) :
    Integrable g ((mu.prod nu).map (fun p : Real × Real => p.1 + p.2)) ↔
      Integrable g mu := by
  have hg0 := hg.1
  obtain ⟨c, hc, hsub⟩ := hg.2
  let A : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have hA : Measurable A := measurable_fst.add measurable_snd
  rw [integrable_map_measure hg_meas.aestronglyMeasurable hA.aemeasurable]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.prod_left_ae.exists
    have hy' : Integrable (fun x : ℝ => g (x + y)) mu := hy
    have hd := (hy'.const_mul c).mul_const (g (-y))
    apply hd.mono hg_meas.aestronglyMeasurable
    filter_upwards [] with x
    have hh := hsub (x + y) (-y)
    rw [add_neg_cancel_right] at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x),
      abs_of_nonneg (mul_nonneg (mul_nonneg hc.le (hg0 (x + y))) (hg0 (-y)))] using hh
  · intro h
    have hd := (h.const_mul c).mul_prod hnu
    apply hd.mono (hg_meas.comp hA).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Function.comp_apply, A, Real.norm_eq_abs,
      abs_of_nonneg (hg0 (z.1 + z.2)),
      abs_of_nonneg (mul_nonneg (mul_nonneg hc.le (hg0 z.1)) (hg0 z.2))] using hsub z.1 z.2
