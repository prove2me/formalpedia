-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionSignedCompactBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:00:25.893551+00:00
-- url     : https://prove2.me/submissions/24500634-a2b5-44be-9057-d98e8863872d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (g : NNReal → ℝ) (hg : IsCadlag g) (c : ℝ) (t : NNReal) :
    BddAbove ((fun s => c * g s) '' Set.Icc 0 t) := by 
  have hc : IsCadlag (fun s => c * g s) := by
    intro v
    refine ⟨continuousWithinAt_const.mul (hg v).1, ?_⟩
    obtain ⟨l, hl⟩ := (hg v).2
    exact ⟨c*l, hl.const_mul c⟩
  apply (Kyprianou.Ch01.cadlag_runningSup_bddAbove (fun s => c * g s) hc t).mono
  rintro z ⟨s,hs,rfl⟩
  exact ⟨s,hs.2,rfl⟩
