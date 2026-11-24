-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpBandFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:20.506465+00:00
-- url     : https://prove2.me/submissions/e9f4b5d1-cf77-4dc7-95fd-7a2a6e4ccd31

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (e : Real) (he : 0 < e) :
    IsFiniteMeasure (T.levyMeasure.restrict {x : Real | e ≤ |x| ∧ |x| < 1}) := by
  apply isFiniteMeasure_restrict.mpr
  let c := ENNReal.ofReal (min 1 (e^2))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (lt_min (by norm_num) (sq_pos_of_pos he)))
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) := by fun_prop
  have hs : {x : ℝ | e ≤ |x| ∧ |x| < 1} ⊆
      {x : ℝ | c ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have h := pow_le_pow_left₀ he.le hx.1 2
    rw [sq_abs] at h
    exact min_le_min le_rfl h
  have hh := mul_meas_ge_le_lintegral hf c (μ := T.levyMeasure)
  exact (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top T.levyMeasure_isLevyMeasure.2.ne hh) hc).ne |> fun h =>
      ne_top_of_le_ne_top h (measure_mono hs)
