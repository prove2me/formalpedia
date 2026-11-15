-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPath_toFoundations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:17:16.707274+00:00
-- url     : https://prove2.me/submissions/7d5a57b6-0bc3-4bbb-a0c8-4178ec95ff5c

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
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    ProbabilityTheory.compoundPoisson b τ Y t ω =
      LevyFoundations.compoundPoisson b τ Y t ω := by
  rfl
