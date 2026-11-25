-- Prove2me | solution 1 for GroundTheory.ProfCoh.sInter_mem_cosetSelectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:33.587025+00:00
-- url     : https://prove2.me/submissions/454a7cfc-e642-4eb3-917a-18507664c79b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_InflationRestriction_Section

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
namespace GroundTheory.ProfCoh
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G))
    {c : Set (Set G)} (hcS : c ⊆ cosetSelectors N) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ⋂₀ c ∈ cosetSelectors N := by
  have : Nonempty c := hne.to_subtype
  choose K hKn hKc hKN hKmul hKex hKuniq using fun T : c => (hcS T.2).2
  refine ⟨isClosed_sInter fun T hT => (hcS hT).1, ⨅ T : c, K T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun n hn g => Subgroup.mem_iInf.2 fun T =>
      (hKn T).conj_mem _ (Subgroup.mem_iInf.1 hn T) g⟩
  · rw [Subgroup.coe_iInf]
    exact isClosed_iInter hKc
  · exact (iInf_le _ (Classical.arbitrary c)).trans (hKN _)
  · intro t ht k hk
    exact Set.mem_sInter.2 fun T hT =>
      hKmul ⟨T, hT⟩ t (Set.mem_sInter.1 ht T hT) k (Subgroup.mem_iInf.1 hk ⟨T, hT⟩)
  · intro x
    have : IsClosed (N : Set G) := hN
    have : T2Space (G ⧸ N) := inferInstance
    have hne' : (⋂ T : c, ((T : Set G) ∩ {t | (t : G ⧸ N) = x})).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro T T'
        rcases hc.total T.2 T'.2 with h | h
        · exact ⟨T, le_rfl, Set.inter_subset_inter_left _ h⟩
        · exact ⟨T', Set.inter_subset_inter_left _ h, le_rfl⟩
      · intro T
        obtain ⟨t, ht, htx⟩ := hKex T x
        exact ⟨t, ht, htx⟩
      · intro T
        exact ((hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)).isCompact
      · intro T
        exact (hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)
    obtain ⟨t, ht⟩ := hne'
    rw [Set.mem_iInter] at ht
    refine ⟨t, Set.mem_sInter.2 fun T hT => (ht ⟨T, hT⟩).1, ?_⟩
    exact (ht (Classical.arbitrary c)).2
  · intro t ht t' ht' h
    exact Subgroup.mem_iInf.2 fun T =>
      hKuniq T t (Set.mem_sInter.1 ht T T.2) t' (Set.mem_sInter.1 ht' T T.2) h
end GroundTheory.ProfCoh
