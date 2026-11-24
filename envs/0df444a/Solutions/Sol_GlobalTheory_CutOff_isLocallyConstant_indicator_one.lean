-- Prove2me | solution 1 for GlobalTheory.CutOff.isLocallyConstant_indicator_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:38.910131+00:00
-- url     : https://prove2.me/submissions/6bbdf746-3e7c-4273-b465-b5891dab04e6

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff
namespace GlobalTheory.CutOff
theorem _root_.solution {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hx, Set.notMem_compl_iff.not.1 (by simpa using hy)]
end GlobalTheory.CutOff
