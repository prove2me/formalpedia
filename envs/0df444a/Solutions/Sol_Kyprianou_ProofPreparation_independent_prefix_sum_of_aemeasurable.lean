-- Prove2me | solution 1 for Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:51.480207+00:00
-- url     : https://prove2.me/submissions/ea5d0a3f-9acc-421d-99c5-771aaeb8b0e2

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

theorem independent_prefix_sum_of_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (N : ℕ → Ω → ℕ)
    (hind : iIndepFun N P)
    (hN : ∀ k, AEMeasurable (N k) P)
    (s : Finset ℕ) (k : ℕ) (hk : k ∉ s) :
    IndepFun (fun ω => ∑ j ∈ s, N j ω) (N k) P := by
  have := hind.indepFun_finsetSum_of_notMem₀ hN hk
  convert this using 1
  funext ω
  simp [Finset.sum_apply]

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (N : ℕ → Ω → ℕ)
    (hind : iIndepFun N P)
    (hN : ∀ k, AEMeasurable (N k) P)
    (s : Finset ℕ) (k : ℕ) (hk : k ∉ s) :
    IndepFun (fun ω => ∑ j ∈ s, N j ω) (N k) P := by
  first
  | exact Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable
  | exact Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable ..
  | (apply Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable <;> assumption)
