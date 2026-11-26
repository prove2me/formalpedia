-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_tail_law_eval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:41:32.992152+00:00
-- url     : https://prove2.me/submissions/9a750810-f353-4648-b7df-2bea448f645e

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- Evaluate the reflected positive-half-line density on a lower-deficit interval. -/
theorem solution (ν : Measure ℝ) (d x : ℝ) (hd : 0 < d) (hx : 0 ≤ x)
    (hfin : ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/d) * ν (Iio (-y)))) (Iic x) ≠ ⊤) :
    (((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/d) * ν (Iio (-y)))).map
      (fun y => -y) (Ici (-x))).toReal =
      (1/d) * ∫ y in Icc 0 x, (ν (Iio (-y))).toReal ∂volume := by
  have ht : Measurable (fun y : ℝ => ν (Iio (-y))) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (Iio_subset_Iio (neg_le_neg hab))
  have he : (fun y : ℝ => -y) ⁻¹' Ici (-x) = Iic x := by
    ext y
    simp
  have hset : Iic x ∩ Ioi (0 : ℝ) = Ioc 0 x := by ext y; simp [and_comm]
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici, he,
    withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, hset,
    lintegral_const_mul _ ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc]
  have hlt : (∫⁻ y in Ioc 0 x, ν (Iio (-y)) ∂volume) ≠ ⊤ := by
    intro h
    apply hfin
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      hset, lintegral_const_mul _ ht, h, ENNReal.mul_top]
    simp [hd, ENNReal.ofReal_eq_zero]
  exact (integral_toReal ht.aemeasurable (ae_lt_top ht hlt)).symm
