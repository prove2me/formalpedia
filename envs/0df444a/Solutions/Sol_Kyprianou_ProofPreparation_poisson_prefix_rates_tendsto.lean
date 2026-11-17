-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:12.219202+00:00
-- url     : https://prove2.me/submissions/1a67240a-9771-4822-8a46-150dc5ffbdb0

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

theorem poisson_prefix_rates_tendsto
    (rate : ℕ → ℝ≥0) (hsum : Summable rate) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, rate k)
      atTop (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) := by
  rw [← ENNReal.coe_tsum hsum, ENNReal.toNNReal_coe]
  exact hsum.hasSum.tendsto_sum_nat

end Kyprianou.ProofPreparation

theorem solution
    (rate : ℕ → ℝ≥0) (hsum : Summable rate) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, rate k)
      atTop (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto
  | exact Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto ..
  | (apply Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto <;> assumption)
