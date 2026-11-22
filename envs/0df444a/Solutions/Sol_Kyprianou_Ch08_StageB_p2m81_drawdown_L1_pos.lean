-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_L1_pos
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:24:07.949946+00:00
-- url     : https://prove2.me/submissions/f7101dad-f690-4a86-b295-ec60740840c7

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-1 * y))) := by fun_prop
  have he := (lintegral_eq_zero_iff hm).mp hz
  have hf : ∀ᵐ y ∂μ, False := he.mono fun y hy =>
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-1 * y)))) hy
  have hzμ : μ = 0 := by simpa using hf
  exact (by simp : μ Set.univ ≠ 0) (by simp [hzμ])
