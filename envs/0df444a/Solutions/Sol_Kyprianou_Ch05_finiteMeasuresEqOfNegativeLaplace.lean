-- Prove2me | solution 1 for Kyprianou.Ch05.finiteMeasuresEqOfNegativeLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:43.447493+00:00
-- url     : https://prove2.me/submissions/c55c40ae-085c-442a-b9fc-670246e6d194

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch04_exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure Real) (hc : mu Set.univ = nu Set.univ)
    (hct : mu Set.univ ≠ ⊤)
    (hfin : ∀ t : Real, 0 < t →
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂mu) < ⊤)
    (heq : ∀ t : Real, 0 < t →
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂mu) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂nu)) :
    mu = nu := by
  by_cases hz : mu Set.univ = 0
  · rw [Measure.measure_univ_eq_zero.mp hz, Measure.measure_univ_eq_zero.mp (hc.symm.trans hz)]
  let c := mu Set.univ
  let m : Measure Real := c⁻¹ • mu
  let n : Measure Real := c⁻¹ • nu
  haveI : IsProbabilityMeasure m := ⟨by
    change (c⁻¹ • mu) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hz hct⟩
  haveI : IsProbabilityMeasure n := ⟨by
    change (c⁻¹ • nu) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hc]
    exact ENNReal.inv_mul_cancel hz hct⟩
  have hmn : m = n := by
    apply Kyprianou.Ch04.exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
    · intro t ht
      change (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂(c⁻¹ • mu)) < ⊤
      rw [lintegral_smul_measure, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hz)) (hfin t ht)
    · intro t ht
      simp only [m, n, lintegral_smul_measure, heq t ht]
  have h := congrArg (fun a : Measure Real => c • a) hmn
  have hcancel : c * c⁻¹ = 1 := ENNReal.mul_inv_cancel hz hct
  simpa only [m, n, smul_smul, hcancel, one_smul] using h
