-- Prove2me | solution 1 for Kyprianou.Ch05.measureEqOfFinitePositiveLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:53:31.911124+00:00
-- url     : https://prove2.me/submissions/33ae5fac-1bdb-4055-a4b1-8cec22d338e5

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_expTiltLaplaceShift
import Theorems.Thm_Kyprianou_Ch05_finiteMeasuresEqOfNegativeLaplace
import Theorems.Thm_AvramDividend_Classical_withDensity_injective_of_everywhere_pos_finite
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure Real)
    (hfin : ∀ theta : Real, 0 < theta →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂mu) < ⊤)
    (heq : ∀ theta : Real, 0 < theta →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂mu) =
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂nu)) :
    mu = nu := by
  let f (x : Real) := ENNReal.ofReal (Real.exp (-x))
  have hf : Measurable f := by fun_prop
  apply AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite
    mu nu f hf (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    (fun x => ENNReal.ofReal_ne_top)
  apply Kyprianou.Ch05.finiteMeasuresEqOfNegativeLaplace
  · rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Measure.restrict_univ]
    simpa [f] using heq 1 zero_lt_one
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (by simpa [f] using hfin 1 zero_lt_one : (∫⁻ x, f x ∂mu) < ⊤).ne
  · intro t ht
    change (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂
      (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (-x))))) < ⊤
    rw [Kyprianou.Ch05.expTiltLaplaceShift]
    exact hfin (t+1) (by linarith)
  · intro t ht
    change (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂
      (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (-x))))) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂
      (nu.withDensity (fun x => ENNReal.ofReal (Real.exp (-x)))))
    rw [Kyprianou.Ch05.expTiltLaplaceShift, Kyprianou.Ch05.expTiltLaplaceShift]
    exact heq (t+1) (by linarith)
