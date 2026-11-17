-- Prove2me | solution 1 for Kyprianou.Ch01.gaussianScaledMarginalCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:50.077444+00:00
-- url     : https://prove2.me/submissions/f4839944-114d-4258-9e38-be6339b055ce

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem solution (v t : ℝ≥0) (xi : ℝ) :
    charFun ((gaussianReal 0 t).map
        (fun x : ℝ => Real.sqrt (v : ℝ) * x)) xi =
      Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  have heq : (fun x : ℝ => Real.sqrt (v : ℝ) * x) =
      (fun x : ℝ => Real.sqrt (v : ℝ) • x) := by
    funext x
    simp only [smul_eq_mul]
  rw [heq, MeasureTheory.charFun_map_smul]
  rw [ProbabilityTheory.charFun_gaussianReal]
  have hv : ((Real.sqrt (v : ℝ) : ℝ) : ℂ) ^ 2 = (v : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (NNReal.coe_nonneg v)
  simp [mul_pow, hv] <;> ring
