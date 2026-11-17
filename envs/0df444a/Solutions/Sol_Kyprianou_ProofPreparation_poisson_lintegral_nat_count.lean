-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_lintegral_nat_count
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:13.6131+00:00
-- url     : https://prove2.me/submissions/e2fc97c9-a3b2-4875-b4a0-12bed019197c

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

theorem poisson_lintegral_nat_count (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ENNReal) ∂(poissonMeasure r) = (r : ENNReal) := by
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * r ^ n / (n)!)) r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero]
    have h1 := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
    rw [mul_one] at h1
    have e : ∀ n : ℕ, (r:ℝ) * (Real.exp (-r) * r ^ n / (n ! : ℝ)) = ((n + 1 : ℕ) : ℝ) * (Real.exp (-r) * r ^ (n+1) / ((n+1)! : ℝ)) := by
      intro n
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    simp only [e] at h1
    exact_mod_cast h1
  rw [← ENNReal.ofReal_coe_nnreal]
  conv_rhs => rw [← hs.tsum_eq]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, smul_eq_mul, mul_comm]

end Kyprianou.ProofPreparation

theorem solution (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ENNReal) ∂(poissonMeasure r) = (r : ENNReal) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_lintegral_nat_count
  | exact Kyprianou.ProofPreparation.poisson_lintegral_nat_count ..
  | (apply Kyprianou.ProofPreparation.poisson_lintegral_nat_count <;> assumption)
