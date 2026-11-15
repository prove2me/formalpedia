-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T20:56:43.144336+00:00
-- url     : https://prove2.me/submissions/ece5b0db-2633-4aaa-8878-67fcf6f485f5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω + Y t ω) := by
  have hboth : ∀ᵐ ω ∂P,
      IsCadlag (fun t => X t ω) ∧ IsCadlag (fun t => Y t ω) :=
    Filter.Eventually.and hX.cadlag_ae hY.cadlag_ae
  filter_upwards [hboth] with ω hxy
  exact hxy.1.add hxy.2
