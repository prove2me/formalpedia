-- Prove2me | solution 1 for GlobalTheory.compact_finite_leftCoset_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:59.708744+00:00
-- url     : https://prove2.me/submissions/b888f34c-cbd5-484d-92f1-6a2075516da4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory
open scoped Pointwise
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk
end GlobalTheory
