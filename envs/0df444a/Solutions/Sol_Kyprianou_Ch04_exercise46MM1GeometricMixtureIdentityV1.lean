-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1GeometricMixtureIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:03:36.793402+00:00
-- url     : https://prove2.me/submissions/d05fbaa7-15b1-4e19-8aaf-259e98100d8e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46GeometricConvolutionLaplaceV2
import Theorems.Thm_Kyprianou_Ch04_exercise46ExponentialDensityLaplaceV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
import Theorems.Thm_Kyprianou_Ch04_exercise46MM1MixtureProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu)
    (nu eta : Measure Real) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (heta : eta = ((volume : Measure Real).restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (mu*Real.exp (-mu*x))))
    (hLaw : ∀ B : Set Real, MeasurableSet B →
      nu B = ∑' n : Nat,
        ((1-ENNReal.ofReal (lambda/mu)) * ENNReal.ofReal (lambda/mu)^n) *
        ((Nat.rec (Measure.dirac (0 : Real)) (fun _ (m : Measure Real) => m.conv eta) n : Measure Real) B)) :
    nu = ENNReal.ofReal (1-lambda/mu) •
      ((Measure.dirac (0 : Real)) +
        ((volume : Measure Real).restrict (Ioi 0)).withDensity
          (fun x => ENNReal.ofReal (lambda*Real.exp (-(mu-lambda)*x)))) := by
  let m : Measure Real := ENNReal.ofReal (1-lambda/mu) •
    ((Measure.dirac (0 : Real)) + ((volume : Measure Real).restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (lambda*Real.exp (-(mu-lambda)*x))))
  letI : IsProbabilityMeasure m :=
    Kyprianou.Ch04.exercise46MM1MixtureProbabilityV1 lambda mu hlambda hmu
  have hm : 0 < mu := hlambda.trans hmu
  have hd : 0 < mu-lambda := sub_pos.mpr hmu
  have hr : 0 ≤ 1-lambda/mu := sub_nonneg.mpr (div_le_one_of_le₀ hmu.le hm.le)
  have hN (s : Real) (hs : 0 < s) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) =
        ENNReal.ofReal ((1-lambda/mu)*(1+lambda/(mu-lambda+s))) := by
    have he := Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1 mu mu s hm.le hm hs.le
    rw [Kyprianou.Ch04.exercise46GeometricConvolutionLaplaceV2 eta nu
      (ENNReal.ofReal (lambda/mu)) s hLaw, heta, he,
      ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (div_nonneg hlambda.le hm.le),
      ← ENNReal.ofReal_mul (div_nonneg hlambda.le hm.le),
      ← ENNReal.ofReal_sub 1 (mul_nonneg (div_nonneg hlambda.le hm.le)
        (div_nonneg hm.le (add_pos hm hs).le)),
      ← ENNReal.ofReal_inv_of_pos (show 0 < 1-lambda/mu*(mu/(mu+s)) by
        have hh : lambda/mu < 1 := (div_lt_one hm).mpr hmu
        have hq : mu/(mu+s) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hq (div_nonneg hlambda.le hm.le)]),
      ← ENNReal.ofReal_mul hr]
    congr 1
    have hden : mu + s - lambda ≠ 0 := by linarith
    field_simp [hm.ne', (add_pos hm hs).ne', (add_pos hd hs).ne', hden]
    <;> ring
  have hM (s : Real) (hs : 0 < s) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂m) =
        ENNReal.ofReal ((1-lambda/mu)*(1+lambda/(mu-lambda+s))) := by
    simp only [m, lintegral_smul_measure, smul_eq_mul, lintegral_add_measure,
      lintegral_dirac, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
    rw [Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1 lambda (mu-lambda) s
      hlambda.le hd hs.le, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (div_nonneg hlambda.le (add_pos hd hs).le),
      ← ENNReal.ofReal_mul hr]
  exact Kyprianou.Ch04.exercise46ProbabilityEqOfFiniteNegativeLaplaceV1 nu m
    (fun s hs => by rw [hN s hs]; exact ENNReal.ofReal_lt_top)
    (fun s hs => (hN s hs).trans (hM s hs).symm)
