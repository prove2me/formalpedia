-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionSupSplitLowerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:27:04.058843+00:00
-- url     : https://prove2.me/submissions/600359b1-8637-4721-98ad-aae1e8946303

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (g : NNReal → ℝ) (a t : NNReal)
    (hb : BddAbove (g '' Set.Icc 0 (a+t)))
    : max (LevyExtrema.SBA.runSup g a) (LevyExtrema.SBA.runSup (fun s => g (a+s) - g a) t + g a) ≤
      LevyExtrema.SBA.runSup g (a+t) := by 
  unfold LevyExtrema.SBA.runSup
  apply max_le
  · apply csSup_le
    · exact ⟨g 0, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
    rintro z ⟨s,hs,rfl⟩
    exact le_csSup hb ⟨s,⟨hs.1,hs.2.trans (le_add_of_nonneg_right (zero_le))⟩,rfl⟩
  · apply (le_sub_iff_add_le).mp
    apply csSup_le
    · exact ⟨g (a+0)-g a, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
    rintro z ⟨s,hs,rfl⟩
    apply sub_le_sub_right
    exact le_csSup hb ⟨a+s,⟨zero_le,add_le_add le_rfl hs.2⟩,rfl⟩
