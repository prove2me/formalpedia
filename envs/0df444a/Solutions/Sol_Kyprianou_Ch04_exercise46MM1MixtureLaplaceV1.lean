-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1MixtureLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:40:49.238802+00:00
-- url     : https://prove2.me/submissions/4462cebc-bbb6-4706-9f8d-822422a74ce7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46ExponentialDensityLaplaceV1
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Laplace transform of the explicit stationary M/M/1 probability measure. -/
theorem solution
    (lambda mu s : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hs : 0 ≤ s) :
    let m : Measure Real := ENNReal.ofReal (1-lambda/mu) •
      ((Measure.dirac (0 : Real)) +
        ((volume : Measure Real).restrict (Ioi 0)).withDensity
          (fun x => ENNReal.ofReal
            (lambda*Real.exp (-(mu-lambda)*x))))
    (∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂m) =
      ENNReal.ofReal ((1-lambda/mu)*(1+lambda/(mu-lambda+s))) := by
  dsimp only
  have hm : 0 < mu := hlambda.trans hmu
  have hd : 0 < mu-lambda := sub_pos.mpr hmu
  have hr : 0 ≤ 1-lambda/mu :=
    sub_nonneg.mpr (div_le_one_of_le₀ hmu.le hm.le)
  simp only [lintegral_smul_measure, smul_eq_mul, lintegral_add_measure,
    lintegral_dirac, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  rw [Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1
    lambda (mu-lambda) s hlambda.le hd hs,
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one
      (div_nonneg hlambda.le (add_pos_of_pos_of_nonneg hd hs).le),
    ← ENNReal.ofReal_mul hr]
