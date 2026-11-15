-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:33:26.43668+00:00
-- url     : https://prove2.me/submissions/3b3894c2-ae92-4492-81d6-721fe2766ca1

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
    (fun ω => X 0 ω + Y 0 ω) = (fun _ => (0 : ℝ)) := by
  rw [hX.start_zero, hY.start_zero]
  funext ω
  simp
