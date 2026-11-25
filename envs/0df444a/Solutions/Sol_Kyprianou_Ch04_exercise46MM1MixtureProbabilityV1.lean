-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1MixtureProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:51:44.415339+00:00
-- url     : https://prove2.me/submissions/75e4f703-cfac-421d-a5f3-cbd89e604b8a

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu) :
    IsProbabilityMeasure
      (ENNReal.ofReal (1 - lambda / mu) •
        ((Measure.dirac (0 : Real)) +
          ((volume : Measure Real).restrict (Ioi 0)).withDensity
            (fun x : Real =>
              ENNReal.ofReal (lambda * Real.exp (-(mu - lambda) * x))))) := by
  have hd : 0 < mu - lambda := sub_pos.mpr hmu
  have hm : 0 < mu := hlambda.trans hmu
  have hI := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).const_mul lambda
  have hL : (∫⁻ x in Ioi (0 : Real),
      ENNReal.ofReal (lambda * Real.exp (-(mu-lambda)*x))) =
      ENNReal.ofReal (lambda / (mu-lambda)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun x => mul_nonneg hlambda.le (Real.exp_pos _).le)]
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd)]
    congr 1
    rw [mul_zero, Real.exp_zero]
    field_simp [hd.ne']
    <;> ring
  constructor
  rw [Measure.smul_apply, Measure.add_apply, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.dirac_apply_of_mem (mem_univ _), Measure.restrict_univ, hL, smul_eq_mul]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (div_nonneg hlambda.le hd.le),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (div_le_one_of_le₀ hmu.le hm.le))]
  rw [show (1 - lambda / mu) * (1 + lambda / (mu-lambda)) = 1 by field_simp [hm.ne', hd.ne'] <;> ring]
