-- Prove2me | solution 1 for GroundTheory.Global.finite_range_of_profinite
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:11:03.696799+00:00
-- url     : https://prove2.me/submissions/ca5c2930-5382-4a9c-aea3-1e19e907f5bf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]


theorem solution (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    Finite f.range := by
  have hk : IsOpen (f.ker : Set G) := by
    obtain ⟨U,hU,hsmall⟩ := hH
    obtain ⟨V,hVU,hV,h1⟩ := mem_nhds_iff.mp hU
    have ho := hV.preimage hf
    obtain ⟨N,hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (show (1:G) ∈ f ⁻¹' V by simpa using h1)
    have hmap : N.toSubgroup.map f = ⊥ := hsmall _ (by
      rintro _ ⟨x,hx,rfl⟩; exact hVU (hN hx))
    apply Subgroup.isOpen_mono (H₁ := N.toSubgroup) _ N.isOpen
    intro x hx; change f x = 1
    have hfx : f x ∈ N.toSubgroup.map f := ⟨x,hx,rfl⟩
    simpa only [hmap,Subgroup.mem_bot] using hfx
  letI : DiscreteTopology (G ⧸ f.ker) := QuotientGroup.discreteTopology hk
  exact (QuotientGroup.quotientKerEquivRange f).finite_iff.mp finite_of_compact_of_discrete
