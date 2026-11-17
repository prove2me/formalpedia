-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prefix_rate_diverges
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:11.589889+00:00
-- url     : https://prove2.me/submissions/bef08dd0-b0f4-4620-90f5-92ce31d12aa8

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

theorem poisson_prefix_rate_diverges
    (rate : ℕ → ℝ≥0)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    Tendsto (fun n => ((∑ k ∈ Finset.range n, rate k) : ℝ))
      atTop atTop := by
  have hns : ¬ Summable rate := by
    intro hs
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2 hs) hdiv
  have := NNReal.not_summable_iff_tendsto_nat_atTop.1 hns
  simpa [NNReal.coe_sum] using NNReal.tendsto_coe_atTop.2 this

end Kyprianou.ProofPreparation

theorem solution
    (rate : ℕ → ℝ≥0)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    Tendsto (fun n => ((∑ k ∈ Finset.range n, rate k) : ℝ))
      atTop atTop := by
  first
  | exact Kyprianou.ProofPreparation.poisson_prefix_rate_diverges
  | exact Kyprianou.ProofPreparation.poisson_prefix_rate_diverges ..
  | (apply Kyprianou.ProofPreparation.poisson_prefix_rate_diverges <;> assumption)
