-- Prove2me | solution 1 for GlobalTheory.WeilM.HaarUniq.indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:07.462933+00:00
-- url     : https://prove2.me/submissions/b98daec3-7ea0-48ca-aea3-4b84544bf27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace GlobalTheory.WeilM.HaarUniq
namespace _root_.GlobalTheory.WeilM.HaarUniq
theorem _root_.solution [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by
  simp only [_root_.GlobalTheory.WeilM.SB, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ (K : Set V)
  · exact ⟨K, K.isOpen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set V)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
end _root_.GlobalTheory.WeilM.HaarUniq
end GlobalTheory.WeilM.HaarUniq
