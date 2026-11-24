-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_isCompact_isOpen_between
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:47.304377+00:00
-- url     : https://prove2.me/submissions/369ae571-1447-4710-9245-3deb62529b7c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_exists_isCompact_isOpen_subset


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
theorem _root_.solution {A V : Set X} (hA : IsCompact A) (hV : IsOpen V)
    (hAV : A ⊆ V) : ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ A ⊆ B ∧ B ⊆ V := by
  have h : ∀ x ∈ A, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ x ∈ B ∧ B ⊆ V := fun x hx =>
    exists_isCompact_isOpen_subset (hV.mem_nhds (hAV hx))
  choose B hBc hBo hxB hBV using h
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : A => B x x.2) (fun x => hBo x x.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩)
  refine ⟨⋃ x ∈ s, B x x.2, s.isCompact_biUnion fun x _ => hBc x x.2,
    isOpen_biUnion fun x _ => hBo x x.2, hs, iUnion₂_subset fun x _ => hBV x x.2⟩
end GroundTheory.Automorphic.Whittaker
