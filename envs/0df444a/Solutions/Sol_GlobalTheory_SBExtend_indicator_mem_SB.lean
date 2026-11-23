-- Prove2me | solution 1 for GlobalTheory.SBExtend.indicator_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:13.397723+00:00
-- url     : https://prove2.me/submissions/74c4ef4f-e22c-48ae-8a4d-7e5fff4d63e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.SBExtend
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
open Matrix Topology
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GlobalTheory.SBExtend
namespace _root_.GlobalTheory.SBExtend
theorem _root_.solution {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]
end _root_.GlobalTheory.SBExtend
end GlobalTheory.SBExtend
