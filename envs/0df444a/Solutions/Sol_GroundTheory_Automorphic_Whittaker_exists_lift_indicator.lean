-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_lift_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:09.914555+00:00
-- url     : https://prove2.me/submissions/aa5f59ca-3621-4ec7-b2b8-bf2085374b5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isCompact_isOpen_inter_eq
import Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U) (hAO : A ⊆ O)
    (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ f ∈ supportedIn U, ∀ x ∈ O, f x = A.indicator 1 x := by
  obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU hAO hAc hAo
  refine ⟨B.indicator 1, ⟨indicator_mem_locallyConstantCompactSupport hBc hBo 1,
    Set.support_indicator_subset.trans hBU⟩, fun x hx => ?_⟩
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := by
      have : x ∈ B ∩ O := by rw [hBO]; exact hxA
      exact this.1
    rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxB]
  · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem]
    intro hxB
    exact hxA (hBO ▸ (⟨hxB, hx⟩ : x ∈ B ∩ O))
end GroundTheory.Automorphic.Whittaker
