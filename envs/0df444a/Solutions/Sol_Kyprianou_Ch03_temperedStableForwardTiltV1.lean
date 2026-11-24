-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableForwardTiltV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:43:22.136905+00:00
-- url     : https://prove2.me/submissions/93b562b0-1996-4cd1-864d-94ae406dcad7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha gamma : ℝ) (hc : 0 < c) (hg : 0 < gamma) :
    Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma =
      (Kyprianou.Ch03.temperedStablePositiveMeasure c alpha 0).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-gamma*x))) := by
  unfold Kyprianou.Ch03.temperedStablePositiveMeasure
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (if 0 < x then
      c * Real.exp (-0*x) / x^(1+alpha) else 0)) := by
    apply Measurable.ennreal_ofReal
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  have hg' : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-gamma*x))) := by fun_prop
  rw [← withDensity_mul _ hf hg']
  congr 1
  funext x
  simp only [Pi.mul_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
    ring
  · simp
