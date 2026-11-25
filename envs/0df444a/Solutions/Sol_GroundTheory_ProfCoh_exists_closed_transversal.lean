-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_closed_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:56.008937+00:00
-- url     : https://prove2.me/submissions/fa9e6f27-4f80-4a68-805c-ceab11dc5445

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_InflationRestriction_Section
import Theorems.Thm_GroundTheory_ProfCoh_univ_mem_cosetSelectors
import Theorems.Thm_GroundTheory_ProfCoh_sInter_mem_cosetSelectors
import Theorems.Thm_GroundTheory_ProfCoh_OpenNormalSubgroup_hasBasis_nhds_one


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
open Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G]
variable [TotallyDisconnectedSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ T : Set G, IsClosed T ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
      ∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t = t' := by
  obtain ⟨T, hTmin⟩ := zorn_superset (cosetSelectors N) fun c hcS hc => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Set.univ, univ_mem_cosetSelectors N hN, fun s hs => absurd hs (Set.notMem_empty s)⟩
    · exact ⟨⋂₀ c, sInter_mem_cosetSelectors N hN hcS hc hne, fun s hs => Set.sInter_subset_of_mem hs⟩
  obtain ⟨hTc, K, hKn, hKc, hKN, hKmul, hKex, hKuniq⟩ := hTmin.prop
  suffices hK : ∀ x ∈ K, x = 1 by
    refine ⟨T, hTc, hKex, fun t ht t' ht' h => ?_⟩
    have := hK _ (hKuniq t ht t' ht' h)
    rw [inv_mul_eq_one] at this
    exact this
  intro x hxK
  by_contra hx1

  have hxnhds : ({x}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hx1)
  obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one (G := G)).mem_iff.mp hxnhds
  have hxU : x ∉ (U : Subgroup G) := fun h => hU h rfl
  let W : Subgroup G := K ⊔ (U : Subgroup G)
  have hWopen : IsOpen (W : Set G) :=
    Subgroup.isOpen_mono le_sup_right U.toOpenSubgroup.isOpen
  have : W.Normal := Subgroup.sup_normal K (U : Subgroup G)
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hWopen
  let r : G ⧸ W → G ⧸ (U : Subgroup G) := fun D => ((Quotient.out D : G) : G ⧸ (U : Subgroup G))
  let T' : Set G := T ∩ {g | (g : G ⧸ (U : Subgroup G)) = r (g : G ⧸ W)}
  have hT'c : IsClosed T' :=
    hTc.inter (isClosed_eq QuotientGroup.continuous_mk
      ((continuous_of_discreteTopology (f := r)).comp QuotientGroup.continuous_mk))
  have hK'n : (K ⊓ (U : Subgroup G)).Normal := Subgroup.normal_inf_normal _ _
  have hT'mem : T' ∈ cosetSelectors N := by
    refine ⟨hT'c, K ⊓ (U : Subgroup G), hK'n,
      hKc.inter U.toOpenSubgroup.isClosed, inf_le_left.trans hKN, ?_, ?_, ?_⟩
    · rintro t ⟨ht, htr⟩ k ⟨hkK, hkU⟩
      refine ⟨hKmul t ht k hkK, ?_⟩
      have h1 : ((t * k : G) : G ⧸ (U : Subgroup G)) = (t : G ⧸ (U : Subgroup G)) :=
        QuotientGroup.eq.mpr (by simpa using (U : Subgroup G).inv_mem hkU)
      have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
        QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hkK))
      simp only [Set.mem_ofPred_eq] at htr ⊢
      rw [h1, h2]
      exact htr
    · intro y
      obtain ⟨t, ht, hty⟩ := hKex y
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W t
      obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp w.2
      refine ⟨t * k, ⟨hKmul t ht k hk, ?_⟩, ?_⟩
      · simp only [Set.mem_ofPred_eq, r]
        have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
          QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hk))
        rw [h2, hw, ← hku, ← mul_assoc]
        exact QuotientGroup.eq.mpr (by convert hu using 1; group)
      · rw [← hty]
        exact QuotientGroup.eq.mpr (by simpa using hKN hk)
    · rintro t ⟨ht, htr⟩ t' ⟨ht', ht'r⟩ h
      have hK1 := hKuniq t ht t' ht' h
      refine ⟨hK1, ?_⟩
      have hW : (t : G ⧸ W) = t' := QuotientGroup.eq.mpr (le_sup_left (b := (U : Subgroup G)) hK1)
      simp only [Set.mem_ofPred_eq] at htr ht'r
      have : (t : G ⧸ (U : Subgroup G)) = t' := by rw [htr, ht'r, hW]
      exact QuotientGroup.eq.mp this
  have hTT' : T ⊆ T' := hTmin.2 hT'mem Set.inter_subset_left
  obtain ⟨t, ht, -⟩ := hKex 1
  have htx : t * x ∈ T := hKmul t ht x hxK

  obtain ⟨t₀, ⟨ht₀, ht₀r⟩, -⟩ := (⟨t, hTT' ht, rfl⟩ : ∃ t₀ ∈ T', t₀ = t)
  have hsame : (t : G ⧸ N) = (t * x : G) := QuotientGroup.eq.mpr (by simpa using hKN hxK)
  have hmem := (hT'mem.2.choose_spec)

  have h1 := (hTT' ht).2
  have h2 := (hTT' htx).2
  have hW : (t : G ⧸ W) = (t * x : G) :=
    QuotientGroup.eq.mpr (by simpa using le_sup_left (b := (U : Subgroup G)) hxK)
  simp only [Set.mem_ofPred_eq] at h1 h2
  have : (t : G ⧸ (U : Subgroup G)) = (t * x : G) := by rw [h1, h2, hW]
  exact hxU (by simpa using QuotientGroup.eq.mp this)
end GroundTheory.ProfCoh
