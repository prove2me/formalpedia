-- Prove2me | solution 1 for GlobalTheory.BI.AbByP.subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:37.877804+00:00
-- url     : https://prove2.me/submissions/91295a09-0520-4301-a5b1-dcde828e6bf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI.AbByP
theorem _root_.solution :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩
end _root_.GlobalTheory.BI.AbByP
end GlobalTheory.BI
