-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46NegativeExponentialTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:00:03.245505+00:00
-- url     : https://prove2.me/submissions/4a325b3a-0da8-485f-aabd-513690d3392b

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (x : Real) (hx : 0 ≤ x) :
    (((volume : Measure Real).restrict (Iio 0)).withDensity
      (fun y => ENNReal.ofReal (lambda * mu * Real.exp (mu*y)))) (Iio (-x)) =
      ENNReal.ofReal (lambda * Real.exp (-mu*x)) := by
  rw [withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict_of_subset (Iio_subset_Iio (by linarith : -x ≤ 0))]
  have hi : IntegrableOn (fun y : Real => lambda * mu * Real.exp (mu*y))
      (Iio (-x)) volume := by
    rw [← integrableOn_Iic_iff_integrableOn_Iio]
    exact (integrableOn_exp_mul_Iic hmu (-x)).const_mul (lambda * mu)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => by positivity)]
  congr 1
  rw [← integral_Iic_eq_integral_Iio, integral_const_mul, integral_exp_mul_Iic hmu]
  field_simp [hmu.ne'] <;> ring
