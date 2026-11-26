-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52PositiveDriverMarksAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:52.115033+00:00
-- url     : https://prove2.me/submissions/fb8a4cca-08d6-4089-b031-695a6503675c

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- All marks of a positive compound Poisson driver are strictly positive almost surely. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    (arrival marks : ℕ → Lambda → ℝ) (F : Measure ℝ)
    (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    ∀ᵐ w ∂Q, ∀ n, 0 < marks n w := by
  rw [ae_all_iff]
  intro n
  have h : Q ((marks n) ⁻¹' Iic (0 : ℝ)) = 0 := by
    rw [← Measure.map_apply (hd.measurable_mark n) measurableSet_Iic,
      (hd.law_mark n).map_eq, hPos]
  rw [ae_iff]
  simp only [not_lt]
  exact h
