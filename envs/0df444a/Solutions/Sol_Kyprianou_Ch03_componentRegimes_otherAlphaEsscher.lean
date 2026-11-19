-- Prove2me | solution 1 for Kyprianou.Ch03.componentRegimes_otherAlphaEsscher
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:07:37.826226+00:00
-- url     : https://prove2.me/submissions/fe6de999-6708-4985-aefb-25276add4f29

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace EssAux

lemma key (c alpha gamma : ℝ) (hc : 0 < c) :
    (Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      Kyprianou.Ch03.temperedStablePositiveMeasure c alpha 0 := by
  unfold Kyprianou.Ch03.temperedStablePositiveMeasure
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (if 0 < x
      then c * Real.exp (-gamma * x) / (x ^ (1 + alpha)) else 0)) := by
    apply Measurable.ennreal_ofReal
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) := by
    fun_prop
  rw [← withDensity_mul _ hf hg]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [neg_zero, zero_mul, Real.exp_zero, mul_one, div_mul_eq_mul_div, mul_assoc,
      ← Real.exp_add]
    simp
  · simp

end EssAux

theorem solution
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ alpha : ℝ, (0 < alpha ∧ alpha < 1) ∨
        (1 < alpha ∧ alpha < 2) →
      (Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
        Kyprianou.Ch03.temperedStablePositiveMeasure c alpha 0) :=
  fun alpha _ => EssAux.key c alpha gamma hc
