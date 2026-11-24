-- Prove2me | solution 1 for Kyprianou.Ch03.supInfCadlagFullRangeBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:48:02.491976+00:00
-- url     : https://prove2.me/submissions/a56a1484-4ff2-41e0-9902-5e0cd80c1612

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch01_cadlag_nnreal_neg
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f : NNReal → Real) (hf : IsCadlag f) (t : NNReal) :
    BddAbove (f '' Set.Icc 0 t) ∧ BddBelow (f '' Set.Icc 0 t) := by
  obtain ⟨b, hb⟩ := Kyprianou.Ch01.cadlag_runningSup_bddAbove f hf t
  obtain ⟨c, hc⟩ := Kyprianou.Ch01.cadlag_runningSup_bddAbove
    (fun s => -f s) (Kyprianou.Ch01.cadlag_nnreal_neg f hf) t
  constructor
  · refine ⟨b, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact hb ⟨s, hs.2, rfl⟩
  · refine ⟨-c, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have h := hc (show -f s ∈ {z : ℝ | ∃ r : NNReal, r ≤ t ∧ z = -f r} from
      ⟨s, hs.2, rfl⟩)
    linarith
