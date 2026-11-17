-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_singleton_probability_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:48.089877+00:00
-- url     : https://prove2.me/submissions/4b0df4d3-1c2f-4068-978a-a0f764a0d8e2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem poisson_singleton_probability_tendsto_zero
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) {k}) atTop (𝓝 0) := by
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_zero]
  apply ENNReal.tendsto_ofReal
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hrate
  have h2 := h.div_const (k ! : ℝ)
  rw [zero_div] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  ring

end Kyprianou.ProofPreparation

theorem solution
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) {k}) atTop (𝓝 0) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_singleton_probability_tendsto_zero
  | exact Kyprianou.ProofPreparation.poisson_singleton_probability_tendsto_zero ..
  | (apply Kyprianou.ProofPreparation.poisson_singleton_probability_tendsto_zero <;> assumption)
