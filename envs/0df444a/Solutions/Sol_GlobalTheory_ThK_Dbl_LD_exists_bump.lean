-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.exists_bump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:18.699532+00:00
-- url     : https://prove2.me/submissions/0873cf31-da65-4d11-b57b-b8e6df3d5d00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_compact_openAddSubgroup
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_indicator_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (V : Type) [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] : ∃ g : V → ℂ, Bump g := by
  obtain ⟨K, hK⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  refine ⟨_, HaarUniq.indicator_mem K hK, fun x => ?_, Set.indicator_of_mem K.zero_mem _⟩
  by_cases h : x ∈ (K : Set V) <;> simp [h]
end GlobalTheory.ThK.Dbl.LD
