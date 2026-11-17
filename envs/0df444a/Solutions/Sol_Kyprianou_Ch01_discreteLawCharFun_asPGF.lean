-- Prove2me | solution 1 for Kyprianou.Ch01.discreteLawCharFun_asPGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:11.935366+00:00
-- url     : https://prove2.me/submissions/e20b6ded-4119-4396-93b0-a8c46834829f

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem solution (G : Measure ℕ) [IsProbabilityMeasure G]
    (xi : ℝ) :
    charFun (G.map (fun k : ℕ => (k : ℝ))) xi =
      ∫ k : ℕ, (Complex.exp (Complex.I * (xi : ℂ))) ^ k ∂G := by
  rw [MeasureTheory.charFun_apply_real]
  have hm : Measurable (fun k : ℕ => (k : ℝ)) := by fun_prop
  have hcast : AEMeasurable (fun k : ℕ => (k : ℝ)) G :=
    hm.aemeasurable
  have hf : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I))
      (G.map (fun k : ℕ => (k : ℝ))) := by
    fun_prop
  rw [MeasureTheory.integral_map hcast hf]
  congr 1
  funext k
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
