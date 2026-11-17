-- Prove2me | solution 2 for Kyprianou.ProofPreparation.poisson_marginal_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:15.140719+00:00
-- url     : https://prove2.me/submissions/8af44f3f-9700-4503-9f77-d6ffbeacd16f

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

theorem aemeasurable_of_poisson_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (r : ℝ≥0) (N : Ω → ℕ)
    (hlaw : P.map N = poissonMeasure r) :
    AEMeasurable N P := by
  by_contra h
  rw [Measure.map_of_not_aemeasurable h] at hlaw
  have := measure_univ (μ := poissonMeasure r)
  rw [← hlaw] at this
  simp at this
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
theorem poisson_marginal_lintegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega -> Nat) (r : NNReal)
    (hX : P.map X = poissonMeasure r) :
    (∫⁻ w, ((X w : Nat) : ENNReal) ∂P) = (r : ENNReal) := by
  have hae : AEMeasurable X P := aemeasurable_of_poisson_law P r X hX
  rw [← poisson_lintegral_nat_count r, ← hX,
    lintegral_map' (measurable_from_nat.aemeasurable) hae]

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega -> Nat) (r : NNReal)
    (hX : P.map X = poissonMeasure r) :
    (∫⁻ w, ((X w : Nat) : ENNReal) ∂P) = (r : ENNReal) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_marginal_lintegral
  | exact Kyprianou.ProofPreparation.poisson_marginal_lintegral ..
  | (apply Kyprianou.ProofPreparation.poisson_marginal_lintegral <;> assumption)
