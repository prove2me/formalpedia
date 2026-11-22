-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:35:47.237521+00:00
-- url     : https://prove2.me/submissions/de6f8dd8-2fd2-4403-a803-55065aa11f80

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer two publicly proved arrival-time regularity theorems through
the source-faithful identification of compound-Poisson driver structures. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (τ marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver τ marks rate jumpLaw Q) :
    (∀ᵐ ω ∂Q, StrictMono (fun n => ProbabilityTheory.arrival τ n ω)) ∧
    (∀ᵐ ω ∂Q,
      Tendsto (fun n => ProbabilityTheory.arrival τ n ω) atTop atTop) := by
  have hLevy : LevyFoundations.IsCompoundPoissonDriver
      τ marks rate jumpLaw Q :=
    { measurable_interarrival := hDriver.measurable_interarrival
      measurable_mark := hDriver.measurable_mark
      indep := hDriver.indep
      law_interarrival := hDriver.law_interarrival
      law_mark := hDriver.law_mark }
  have hStrict :
      ∀ᵐ ω ∂Q, StrictMono (fun n => LevyFoundations.arrival τ n ω) :=
    levy_foundations_compoundDriverArrivalStrictMono hLevy hRate
  have hDiverge :
      ∀ᵐ ω ∂Q, Tendsto (fun n => LevyFoundations.arrival τ n ω) atTop atTop :=
    levy_foundations_compoundDriverArrivalDiverges hLevy hRate
  constructor
  · simpa only [ProbabilityTheory.arrival, LevyFoundations.arrival] using hStrict
  · simpa only [ProbabilityTheory.arrival, LevyFoundations.arrival] using hDiverge
