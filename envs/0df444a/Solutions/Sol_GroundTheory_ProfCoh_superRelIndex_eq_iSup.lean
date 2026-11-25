-- Prove2me | solution 1 for GroundTheory.ProfCoh.superRelIndex_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:08.066488+00:00
-- url     : https://prove2.me/submissions/8f8182bd-e027-4e9f-b685-56d876315262

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Theorems.Thm_GroundTheory_ProfCoh_sup_subgroupOf_eq
import Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_dvd_iff_le
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_dvd_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat
attribute [local simp] GroundTheory.ProfCoh.Supernatural.ofNat_one



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superRelIndex K H =
      ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by

  let res : OpenNormalSubgroup G → OpenNormalSubgroup H := fun U =>
    { toSubgroup := (U : Subgroup G).subgroupOf H
      isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
      isNormal' := inferInstance }
  have hres : ∀ U : OpenNormalSubgroup G,
      K.subgroupOf H ⊔ ((res U : OpenNormalSubgroup H) : Subgroup H) =
        (K ⊔ (U : Subgroup G)).subgroupOf H :=
    fun U => (sup_subgroupOf_eq hKH).symm
  refine le_antisymm (iSup_le fun V => ?_) (iSup_le fun U => ?_)
  ·
    obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
    have h1W : (1 : G) ∈ W := by
      have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
      simpa using this
    obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
    refine le_iSup_of_le U ?_
    have hle : (K ⊔ (U : Subgroup G)).subgroupOf H ≤ K.subgroupOf H ⊔ (V : Subgroup H) := by
      rw [← hres U]
      refine sup_le_sup_left (fun x hx => ?_) _
      have : (x : G) ∈ W := hUW hx
      have : x ∈ Subtype.val ⁻¹' W := this
      rw [hWV] at this
      exact this
    have hne : ((K ⊔ (U : Subgroup G)).subgroupOf H).index ≠ 0 := relIndex_sup_ne_zero K H U
    show Supernatural.ofNat _ ≤ Supernatural.ofNat ((K ⊔ (U : Subgroup G)).subgroupOf H).index
    rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat
      (fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))) hne]
    exact Subgroup.index_dvd_of_le hle
  · refine le_iSup_of_le (res U) ?_
    rw [hres U]
    exact le_rfl
end GroundTheory.ProfCoh
