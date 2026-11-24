-- Prove2me | solution 1 for Kyprianou.Ch02.smallJumpBandMeasureFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:50:09.29044+00:00
-- url     : https://prove2.me/submissions/7301ae02-fa81-42ba-a664-c1e42c2db790

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (e : ℝ) (he : 0 < e) :
    levyMeasure {x : ℝ | e ≤ |x| ∧ |x| < 1} < ⊤ := by
  let B : Set ℝ := {x | e ≤ |x| ∧ |x| < 1}
  let c : ENNReal := ENNReal.ofReal (min 1 (e ^ 2))
  let f : ℝ → ENNReal := fun x => ENNReal.ofReal (min 1 (x ^ 2))
  have hc_pos : 0 < c :=
    ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos he))
  have hf_meas : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.min (measurable_id'.pow_const 2)
  have hsub : B ⊆ {x : ℝ | c ≤ f x} := by
    intro x hx
    simp only [B, Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min le_rfl
      ((sq_abs x).symm ▸ pow_le_pow_left₀ he.le hx.1 2)
  have hMarkov := mul_meas_ge_le_lintegral hf_meas c (μ := levyMeasure)
  have hle : c * levyMeasure B ≤ ∫⁻ x, f x ∂levyMeasure :=
    le_trans (mul_le_mul_right (measure_mono hsub) c) hMarkov
  exact ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top hlevyMeasure.2.ne hle) hc_pos.ne'
