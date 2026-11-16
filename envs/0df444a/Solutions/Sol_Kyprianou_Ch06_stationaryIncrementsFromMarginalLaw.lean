-- Prove2me | solution 1 for Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:03:20.101733+00:00
-- url     : https://prove2.me/submissions/1af981aa-97ce-4579-b116-e789b60e397d

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Chapter 6 real Lévy-process stationary increment law, transferred to the
published IdentDistrib interface using only the almost-sure initial condition.
The hypotheses are exact components of Chapter 6 IsRealLevyProcess. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t)) :
    ProbabilityTheory.HasStationaryIncrements X P := by
  intro s t
  have hzeroeq : (fun ω => X t ω - X 0 ω) =ᵐ[P] X t := by
    filter_upwards [hzero] with ω hω
    simp [hω]
  have hmapzero :
      P.map (ProbabilityTheory.increment X 0 t) = P.map (X t) := by
    exact Measure.map_congr hzeroeq
  have heq : P.map (ProbabilityTheory.increment X s (s + t)) =
      P.map (ProbabilityTheory.increment X 0 t) := by
    calc
      P.map (ProbabilityTheory.increment X s (s + t)) =
          P.map (X t) := by
        change P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t)
        exact hlaw s t
      _ = P.map (ProbabilityTheory.increment X 0 t) := hmapzero.symm
  refine ⟨?_, ?_, heq⟩
  · exact ((hmeas (s + t)).sub (hmeas s)).aemeasurable
  · exact ((hmeas t).sub (hmeas 0)).aemeasurable
