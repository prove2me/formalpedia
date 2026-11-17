-- Prove2me | solution 2 for Kyprianou.ProofPreparation.poisson_bounded_count_probability_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:48.796203+00:00
-- url     : https://prove2.me/submissions/fc1a86d3-f6d0-40ca-9f4c-783b8bf1e306

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
theorem poisson_bounded_count_probability_tendsto_zero
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) (Set.Iic k))
      atTop (𝓝 0) := by
  have hset : (Set.Iic k : Set ℕ) = ((Finset.range (k+1) : Finset ℕ) : Set ℕ) := by
    ext j; simp [Nat.lt_succ_iff]
  simp_rw [hset, ← sum_measure_singleton]
  have : (0 : ℝ≥0∞) = ∑ j ∈ Finset.range (k+1), (0 : ℝ≥0∞) := by simp
  rw [this]
  exact tendsto_finset_sum _ fun j _ => poisson_singleton_probability_tendsto_zero rate hrate j

end Kyprianou.ProofPreparation

theorem solution
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) (Set.Iic k))
      atTop (𝓝 0) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_bounded_count_probability_tendsto_zero
  | exact Kyprianou.ProofPreparation.poisson_bounded_count_probability_tendsto_zero ..
  | (apply Kyprianou.ProofPreparation.poisson_bounded_count_probability_tendsto_zero <;> assumption)
