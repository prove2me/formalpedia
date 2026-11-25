-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_isCompact_subset_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:44.701105+00:00
-- url     : https://prove2.me/submissions/1fb74ba7-e4af-4ff5-9e76-51b6f41ae077

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_nhds_inter_doubleCoset_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Topology Set DoubleCoset
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]
variable {P Q : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {Kc : Set G} (hK : IsCompact Kc) (hKC : Kc ⊆ doubleCoset x (P : Set G) Q) :
    ∃ L : Set G, IsCompact L ∧ L ⊆ Q ∧ ∀ z ∈ Kc, ∃ p ∈ P, ∃ l ∈ L, z = p * x * l := by
  obtain ⟨K₁, hK₁c, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hloc : ∀ c ∈ Kc, ∃ V ∈ 𝓝 c, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ (univ : Set G) ∧ ∃ q ∈ Q, q ∈ K₁ ∧ z = p * c * q :=
    fun c hc => exists_nhds_inter_doubleCoset_subset hP hQ hC (hKC hc) Filter.univ_mem hK₁
  choose V hV hVsub using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' V hV
  have hq : ∀ c : Kc, ∃ p ∈ P, ∃ q ∈ Q, (c : G) = p * x * q := fun c => mem_doubleCoset.1 (hKC c.2)
  choose pc hpc qc hqc hcq using hq
  refine ⟨⋃ c ∈ t, (fun z => qc c * z) '' ((Q : Set G) ∩ K₁), ?_, ?_, ?_⟩
  · exact t.isCompact_biUnion fun c _ =>
      (hK₁c.inter_left hQ).image (continuous_const.mul continuous_id)
  · intro l hl
    simp only [Set.mem_iUnion, Set.mem_image] at hl
    obtain ⟨c, _, z, hz, rfl⟩ := hl
    exact Q.mul_mem (hqc c) hz.1
  · intro z hz
    have hz' := ht hz
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    obtain ⟨p, hp, -, q, hq, hqK, rfl⟩ := hVsub c c.2 z hzc (hKC hz)
    refine ⟨p * pc c, P.mul_mem hp (hpc c), qc c * q, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨c, hct, q, ⟨hq, hqK⟩, rfl⟩
    · rw [hcq c]
      group
end GroundTheory.Automorphic.Parabolic
