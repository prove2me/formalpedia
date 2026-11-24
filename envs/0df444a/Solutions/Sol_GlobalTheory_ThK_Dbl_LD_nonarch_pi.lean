-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.nonarch_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:46.355066+00:00
-- url     : https://prove2.me/submissions/9a999d05-e3f6-46ef-a802-b79d0ec1561e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA

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
theorem _root_.solution (ι V : Type) [Finite ι] [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] :
    NonarchimedeanAddGroup (ι → V) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hU⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i).toAddSubgroup, isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩,
      fun x hx => hU fun i _ => hK i (hx i trivial)⟩
end GlobalTheory.ThK.Dbl.LD
