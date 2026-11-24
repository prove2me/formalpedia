-- Prove2me | solution 1 for GlobalTheory.LocFlat.flatSB_isLocallyConstant_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:31.721337+00:00
-- url     : https://prove2.me/submissions/24d9ebc4-9b02-42a1-b5f7-6fbd6481ad5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution {X : Type*} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    (a : ℂ) : IsLocallyConstant (W.indicator fun _ => a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
end GlobalTheory.LocFlat
