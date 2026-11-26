-- Prove2me | solution 1 for GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:03:31.765499+00:00
-- url     : https://prove2.me/submissions/444ce233-ec7d-46b7-a1f5-15e926a6b479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetLeftTransversalOfRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
theorem _root_.solution : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K hKH hfin
  classical
  have : Finite (H ⧸ K.subgroupOf H) := by
    have h : (K.subgroupOf H).index ≠ 0 := hfin
    exact (Subgroup.index_ne_zero_iff_finite.1 h)
  have := Fintype.ofFinite (H ⧸ K.subgroupOf H)
  set rep : H ⧸ K.subgroupOf H → G := fun q => ((q.out : H) : G) with hrep
  have key : ∀ (a b : H), (QuotientGroup.mk a : H ⧸ K.subgroupOf H) = QuotientGroup.mk b ↔ (a : G)⁻¹ * (b : G) ∈ K := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hr
    exact (q.out).2
  · intro k hk
    set q : H ⧸ K.subgroupOf H := QuotientGroup.mk ⟨k, hk⟩ with hq
    have h1 : (rep q)⁻¹ * k ∈ K := by
      have := (key q.out ⟨k, hk⟩).1 (by rw [QuotientGroup.out_eq'])
      exact this
    refine ⟨rep q, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), h1⟩, ?_⟩
    rintro r ⟨hr, hrk⟩
    obtain ⟨q', _, rfl⟩ := Finset.mem_image.1 hr
    have : q' = q := by
      have h2 := (key q'.out ⟨k, hk⟩).2 hrk
      rwa [QuotientGroup.out_eq'] at h2
    rw [this]

