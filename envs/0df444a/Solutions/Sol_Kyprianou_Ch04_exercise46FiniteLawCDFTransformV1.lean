-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FiniteLawCDFTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:19:45.717422+00:00
-- url     : https://prove2.me/submissions/7e0e055f-4672-4988-b954-2f8e4d308bf4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Apply the nonnegative cumulative transform and take real parts. -/
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hsupp : nu (Iio (0 : Real)) = 0)
    (beta : Real) (hb : 0 < beta) :
    beta * (∫ t in Ici (0 : Real),
      Real.exp (-beta * t) * (nu (Iic t)).toReal ∂volume) =
      ∫ y, Real.exp (-beta * y) ∂nu := by
  let e : Real → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-beta * t))
  have he : Measurable e := by fun_prop
  have hc : Measurable (fun t : Real => nu (Iic t)) :=
    (show Monotone (fun t : Real => nu (Iic t)) from
      fun _ _ h => measure_mono (Iic_subset_Iic.mpr h)).measurable
  have h1 := integral_toReal (μ := volume.restrict (Ioi (0 : Real)))
    (he.mul hc).aemeasurable (Eventually.of_forall fun t =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top nu (Iic t)))
  have h2 := integral_toReal (μ := nu) he.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
  simp only [Pi.mul_apply, e, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h1 h2
  rw [integral_Ici_eq_integral_Ioi, h1, h2,
    AvramDividend.Classical.positiveLaplace_cumulative_measure nu beta hb hsupp,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / beta)]
  field_simp
