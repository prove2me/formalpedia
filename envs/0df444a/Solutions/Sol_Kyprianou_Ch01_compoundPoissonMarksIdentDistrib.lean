-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonMarksIdentDistrib
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:04:07.481446+00:00
-- url     : https://prove2.me/submissions/0ca2d435-2422-47c0-b577-dae8e97b4541

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival marks : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw P) :
    ∀ n : ℕ, IdentDistrib (marks n) (marks 0) P P := by
  intro n
  exact ⟨(hdriver.measurable_mark n).aemeasurable, (hdriver.measurable_mark 0).aemeasurable,
    by rw [(hdriver.law_mark n).map_eq, (hdriver.law_mark 0).map_eq]⟩
