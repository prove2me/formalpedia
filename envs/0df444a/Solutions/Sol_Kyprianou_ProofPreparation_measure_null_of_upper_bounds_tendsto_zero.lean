-- Prove2me | solution 1 for Kyprianou.ProofPreparation.measure_null_of_upper_bounds_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:07.951202+00:00
-- url     : https://prove2.me/submissions/86792eac-53a4-41b9-b92c-639d31565479

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

theorem measure_null_of_upper_bounds_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (b : ℕ → ENNReal)
    (hupper : ∀ n, P A ≤ b n)
    (hzero : Tendsto b atTop (𝓝 0)) :
    P A = 0 :=
  le_antisymm (ge_of_tendsto' hzero hupper) bot_le

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (b : ℕ → ENNReal)
    (hupper : ∀ n, P A ≤ b n)
    (hzero : Tendsto b atTop (𝓝 0)) :
    P A = 0 := by
  first
  | exact Kyprianou.ProofPreparation.measure_null_of_upper_bounds_tendsto_zero
  | exact Kyprianou.ProofPreparation.measure_null_of_upper_bounds_tendsto_zero ..
  | (apply Kyprianou.ProofPreparation.measure_null_of_upper_bounds_tendsto_zero <;> assumption)
