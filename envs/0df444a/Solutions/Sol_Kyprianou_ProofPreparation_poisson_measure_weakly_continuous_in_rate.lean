-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_measure_weakly_continuous_in_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:54:05.295201+00:00
-- url     : https://prove2.me/submissions/78f01c8d-dee8-4c83-9423-cf6e8c637d6d

import Mathlib
import Definitions.Def_Kyprianou_ProofPreparation_realPoissonProbability
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_charfun_continuous_in_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

/-- Weak continuity of the Poisson law under a converging rate. -/
theorem solution
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => realPoissonProbability (rate n))
      atTop (𝓝 (realPoissonProbability r)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto
    (fun n : ℕ => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t) atTop
      (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t))
  exact poisson_charfun_continuous_in_rate rate r hrate t
