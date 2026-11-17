-- Prove2me | solution 2 for Kyprianou.ProofPreparation.poisson_measure_weakly_continuous_in_rate
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:12:50.096062+00:00
-- url     : https://prove2.me/submissions/130e2341-8d16-43dd-b6e8-f6e7f53c91b9

import Mathlib
import Definitions.Def_Kyprianou_ProofPreparation_realPoissonProbability
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
noncomputable section

theorem poisson_charfun_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun n => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t)
      atTop (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t)) := by
  simp_rw [charFun_map_cast_poissonMeasure]
  apply Tendsto.cexp
  apply Tendsto.mul_const
  have h1 : Tendsto (fun n => ((rate n : ℝ) : ℂ)) atTop (𝓝 ((r : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((NNReal.continuous_coe.tendsto r).comp hrate)
  simpa using h1

theorem poisson_measure_weakly_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => realPoissonProbability (rate n))
      atTop (𝓝 (realPoissonProbability r)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  exact poisson_charfun_continuous_in_rate rate r hrate t

end
end Kyprianou.ProofPreparation

open MeasureTheory ProbabilityTheory Filter Complex in
open scoped NNReal ENNReal Nat Topology in
theorem solution
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => Kyprianou.ProofPreparation.realPoissonProbability (rate n))
      atTop (𝓝 (Kyprianou.ProofPreparation.realPoissonProbability r)) :=
  Kyprianou.ProofPreparation.poisson_measure_weakly_continuous_in_rate rate r hrate
