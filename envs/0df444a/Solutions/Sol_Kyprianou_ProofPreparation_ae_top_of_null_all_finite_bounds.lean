-- Prove2me | solution 1 for Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:10.634203+00:00
-- url     : https://prove2.me/submissions/1d149c50-f053-4342-8cf1-896483012f78

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

theorem ae_top_of_null_all_finite_bounds
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ENNReal)
    (hnull : ∀ m : ℕ, P {ω | f ω ≤ (m : ENNReal)} = 0) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by
  rw [ae_iff]
  apply measure_mono_null _ (measure_iUnion_null hnull)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hω
  exact Set.mem_iUnion.2 ⟨m, hm.le⟩

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ENNReal)
    (hnull : ∀ m : ℕ, P {ω | f ω ≤ (m : ENNReal)} = 0) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by
  first
  | exact Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds
  | exact Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds ..
  | (apply Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds <;> assumption)
