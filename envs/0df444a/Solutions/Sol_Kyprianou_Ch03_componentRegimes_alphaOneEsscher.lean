-- Prove2me | solution 1 for Kyprianou.Ch03.componentRegimes_alphaOneEsscher
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:07:36.510196+00:00
-- url     : https://prove2.me/submissions/8faeeb71-3024-4584-9e1f-8ebedeeb70a9

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
    (Kyprianou.Ch03.temperedStablePositiveMeasure c 1 gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      Kyprianou.Ch03.temperedStablePositiveMeasure c 1 0 :=
  EssAux.key c 1 gamma hc
