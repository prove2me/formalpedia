-- Prove2me | solution 1 for ItoLemma.continuous_adapted_composition_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:52:25.053145+00:00
-- url     : https://prove2.me/submissions/7e131fdd-be3a-43ca-9ef1-1868d1b4b305

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyStochCalc
open Filter Topology

universe u

/-- A continuous functional of a continuous adapted two-coordinate process
is progressively measurable with respect to the same filtration. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {Y : ℝ → Ω → (Fin 2 → ℝ)}
    (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYa : ∀ t, Measurable[ℱ t] (Y t))
    {φ : (Fin 2 → ℝ) → ℝ} (hφ : Continuous φ) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => φ (Y s ω)) :=
  Probability.progressivelyMeasurable_of_rightContinuous (X := fun s ω => φ (Y s ω))
    (fun t => hφ.measurable.comp (hYa t))
    (fun ω t => ((hφ.comp (hYc ω)).tendsto t).mono_left nhdsWithin_le_nhds)
