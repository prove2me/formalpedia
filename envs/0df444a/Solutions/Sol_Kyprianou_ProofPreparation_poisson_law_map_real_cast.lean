-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_law_map_real_cast
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:14.455177+00:00
-- url     : https://prove2.me/submissions/eed63094-32ec-41ae-8f35-3a651752c7b3

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

theorem poisson_law_map_real_cast
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℕ) (r : ℝ≥0)
    (hlaw : P.map X = poissonMeasure r)
    (hX : AEMeasurable X P) :
    P.map (fun ω => (X ω : ℝ)) =
      (poissonMeasure r).map (Nat.cast : ℕ → ℝ) := by
  rw [← hlaw, AEMeasurable.map_map_of_aemeasurable (measurable_from_nat.aemeasurable) hX]
  rfl

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℕ) (r : ℝ≥0)
    (hlaw : P.map X = poissonMeasure r)
    (hX : AEMeasurable X P) :
    P.map (fun ω => (X ω : ℝ)) =
      (poissonMeasure r).map (Nat.cast : ℕ → ℝ) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_law_map_real_cast
  | exact Kyprianou.ProofPreparation.poisson_law_map_real_cast ..
  | (apply Kyprianou.ProofPreparation.poisson_law_map_real_cast <;> assumption)
