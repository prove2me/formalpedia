-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_l1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T02:48:36.01074+00:00
-- url     : https://prove2.me/submissions/761c0fab-d32e-4daa-ac9c-359ff28379d6

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap
open MeasureTheory ProbabilityTheory Filter Set Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    0 < ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ).toReal) ∧
    ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ).toReal) ≤ 1 := by
  have hle := Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap μ hsupp
  have hposE : 0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) := by
    have hmeas : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-1 * y)) : ℝ → ℝ≥0∞) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).measurable
    have hne : ∀ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ≠ 0 :=
      fun y => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    have hsup : Function.support (fun y : ℝ => ENNReal.ofReal (Real.exp (-1 * y))) = Set.univ :=
      Set.eq_univ_of_forall fun y => Function.mem_support.mpr (hne y)
    rw [MeasureTheory.lintegral_pos_iff_support hmeas, hsup, MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact zero_lt_one
  have hne0 : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≠ 0 := ne_of_gt hposE
  have hnetop : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hposR := ENNReal.toReal_pos hne0 hnetop
  have hleR : (((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ).toReal)) ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_lt_top.ne hle; simpa using h
  exact ⟨hposR, hleR⟩
