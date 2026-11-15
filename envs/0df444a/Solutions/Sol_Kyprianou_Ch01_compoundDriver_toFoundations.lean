-- Prove2me | solution 1 for Kyprianou.Ch01.compoundDriver_toFoundations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:16:33.026635+00:00
-- url     : https://prove2.me/submissions/1010c236-eb66-4749-a597-7a4e7a6917ac

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν : Measure ℝ}
    {P : Measure Ω}
    (hd : ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν P) :
    LevyFoundations.IsCompoundPoissonDriver τ Y r ν P := by
  exact {
    measurable_interarrival := hd.measurable_interarrival
    measurable_mark := hd.measurable_mark
    indep := hd.indep
    law_interarrival := hd.law_interarrival
    law_mark := hd.law_mark
  }
