-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_isProSylow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:52.575028+00:00
-- url     : https://prove2.me/submissions/ce97f7d9-b9b3-434c-a61b-7d00cb1f8a3c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
import Theorems.Thm_GroundTheory_ProfCoh_isProSylow_iff
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_subgroup_iff_isPGroup_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Pointwise CategoryTheory
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.ProfCoh
theorem _root_.solution {H : Subgroup G} (hH : IsProPGroup p H) :
    ∃ P : Subgroup G, IsProSylow p P ∧ H ≤ P := by
  rw [isProPGroup_subgroup_iff_isPGroup_map] at hH
  have hfin : ∀ U, Finite ((sylowSystem p H).obj U) := fun U => by
    have := Sylow.finite_of_finiteIndex (default : Sylow p (G ⧸ (U : Subgroup G)))
    exact Subtype.finite
  have hne : ∀ U, Nonempty ((sylowSystem p H).obj U) := fun U => by
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hH U)
    exact ⟨⟨S, hS⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (sylowSystem p H)

  let T : OpenNormalSubgroup G → Subgroup G := fun U =>
    ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).comap (QuotientGroup.mk' (U : Subgroup G))
  have hc : ∀ {U V : OpenNormalSubgroup G} (h : U ≤ V),
      ((s V).1 : Subgroup (G ⧸ (V : Subgroup G))) =
        ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap h) := by
    intro U V h
    rw [← hs (homOfLE h)]
    rfl
  have hHT : ∀ U, H ≤ T U := fun U => Subgroup.map_le_iff_le_comap.mp (s U).2
  have hUT : ∀ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ T U := fun U x hx => by
    show QuotientGroup.mk' (U : Subgroup G) x ∈ ((s U).1 : Subgroup _)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hTcl : ∀ U, IsClosed (T U : Set G) := fun U =>
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (hUT U) U.toOpenSubgroup.isOpen)
  have hTmono : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → T U ≤ T V := fun {U V} h x hx => by
    show QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _)
    rw [hc h]
    exact Subgroup.mem_map_of_mem (quotMap h) hx
  have hTlift : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → ∀ x ∈ T V,
      ∃ y ∈ T U, y⁻¹ * x ∈ (V : Subgroup G) := fun {U V} h x hx => by
    have hx' : QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _) := hx
    rw [hc h] at hx'
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    exact ⟨y, hz, QuotientGroup.eq.mp hzx⟩
  let P : Subgroup G := ⨅ U, T U
  have hPcl : IsClosed (P : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter hTcl
  have hPmap : ∀ U : OpenNormalSubgroup G,
      P.map (QuotientGroup.mk' (U : Subgroup G)) = ((s U).1 : Subgroup _) := by
    intro U
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (iInf_le T U)) fun z hz => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    have hx : x ∈ T U := hz

    let t : OpenNormalSubgroup G → Set G := fun W =>
      (T (W ⊓ U) : Set G) ∩ {y | x⁻¹ * y ∈ (U : Subgroup G)}
    have htcl : ∀ W, IsClosed (t W) := fun W =>
      (hTcl _).inter ((Subgroup.isClosed_of_isOpen _ U.toOpenSubgroup.isOpen).preimage
        (continuous_const_mul x⁻¹))
    have htdir : Directed (· ⊇ ·) t := fun W₁ W₂ =>
      ⟨W₁ ⊓ W₂, fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_left) hy.1, hy.2⟩,
        fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_right) hy.1, hy.2⟩⟩
    have htne : ∀ W, (t W).Nonempty := fun W => by
      obtain ⟨y, hy, hyx⟩ := hTlift (inf_le_right : W ⊓ U ≤ U) x hx
      refine ⟨y, hy, ?_⟩
      have := (U : Subgroup G).inv_mem hyx
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htdir
      htne (fun W => (htcl W).isCompact) htcl
    rw [Set.mem_iInter] at hy
    have hyP : y ∈ P := Subgroup.mem_iInf.mpr fun W => hTmono inf_le_left (hy W).1
    refine Subgroup.mem_map.mpr ⟨y, hyP, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr (hy U).2).symm
  refine ⟨P, (isProSylow_iff hPcl).mpr fun U => ?_, le_iInf fun U => hHT U⟩
  rw [hPmap U]
  exact ⟨(s U).1.isPGroup', (s U).1.not_dvd_index⟩
end GroundTheory.ProfCoh
