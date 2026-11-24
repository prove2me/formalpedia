-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionSupSplitUpperV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:27:12.470035+00:00
-- url     : https://prove2.me/submissions/bde74993-b631-4790-be29-3d40369bc145

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
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
    : LevyExtrema.SBA.runSup g (a+t) ≤
      max (LevyExtrema.SBA.runSup g a) (LevyExtrema.SBA.runSup (fun s => g (a+s) - g a) t + g a) := by 
  let G : NNReal → ℝ := fun s => g (a+s) - g a
  have hG : BddAbove (G '' Set.Icc 0 t) := by
    obtain ⟨b,hb'⟩ := hb
    refine ⟨b-g a, ?_⟩
    rintro z ⟨s,hs,rfl⟩
    apply sub_le_sub_right
    exact hb' ⟨a+s, ⟨zero_le, add_le_add le_rfl hs.2⟩, rfl⟩
  have ha : BddAbove (g '' Set.Icc 0 a) := hb.mono (by
    rintro z ⟨s,hs,rfl⟩
    exact ⟨s, ⟨hs.1,hs.2.trans (le_add_of_nonneg_right (zero_le))⟩,rfl⟩)
  unfold LevyExtrema.SBA.runSup
  apply csSup_le
  · exact ⟨g 0, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
  rintro z ⟨s,hs,rfl⟩
  by_cases hsa : s ≤ a
  · exact le_max_of_le_left (le_csSup ha ⟨s,⟨hs.1,hsa⟩,rfl⟩)
  · have hd : s-a ≤ t := tsub_le_iff_left.mpr (by simpa [add_comm] using hs.2)
    have he : a+(s-a) = s := add_tsub_cancel_of_le (le_of_not_ge hsa)
    have hv := le_csSup hG (show G (s-a) ∈ G '' Set.Icc 0 t from
      ⟨s-a,⟨zero_le,hd⟩,rfl⟩)
    apply le_max_of_le_right
    change g (a+(s-a)) - g a ≤ sSup (G '' Set.Icc 0 t) at hv
    rw [he] at hv
    exact (sub_le_iff_le_add.mp hv)
