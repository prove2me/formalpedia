-- Prove2me | solution 1 for GlobalTheory.PeriodicPartition.exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:08.281719+00:00
-- url     : https://prove2.me/submissions/513b2515-c3a3-47af-8d29-c3b9dd423c57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Theorems.Thm_GlobalTheory_PeriodicPartition_exists_periodic_bump
import Theorems.Thm_GlobalTheory_PeriodicPartition_exists_finite_subcover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicPartition
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory.PeriodicPartition
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ι : Type} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hper : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) (hcov : ∀ z, ∃ i, z ∈ U i) :
    ∃ (s : Finset ι) (ρ : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧
      (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧
      ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  classical
  choose c hc using hcov
  choose ψ hψs hψp hψU hψ0 hψx using fun x => exists_periodic_bump Λ (hU (c x)) (hper (c x)) (hc x)
  obtain ⟨t, ht⟩ := exists_finite_subcover Λ (fun x => {z | 0 < ψ x z})
    (fun x => isOpen_lt continuous_const (hψs x).continuous)
    (fun x l z hz => by simpa [hψp] using hz) (fun z => ⟨z, hψx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ t, ψ x z := fun z => by
    obtain ⟨x, hx, hz⟩ := ht z
    exact Finset.sum_pos' (fun x _ => hψ0 x z) ⟨x, hx, hz⟩
  refine ⟨t.image c, fun i z => (∑ x ∈ t with c x = i, ψ x z) / ∑ x ∈ t, ψ x z,
    fun i => ⟨?_, ?_, ?_⟩, fun z => ?_⟩
  · exact (ContDiff.sum fun x _ => hψs x).div (ContDiff.sum fun x _ => hψs x) fun z => (hS z).ne'
  · intro l z
    simp only [hψp]
  · have hcl : IsClosed (⋃ x ∈ t.filter (fun x => c x = i), tsupport (ψ x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal ?_ hcl).trans ?_
    · intro z hz
      by_contra hn
      refine hz ?_
      have : ∑ x ∈ t with c x = i, ψ x z = 0 := Finset.sum_eq_zero fun x hx => by
        by_contra h
        exact hn (Set.mem_iUnion₂.2 ⟨x, hx, subset_tsupport _ h⟩)
      simp only [this, zero_div]
    · refine Set.iUnion₂_subset fun x hx => ?_
      rw [← (Finset.mem_filter.1 hx).2]
      exact hψU x
  · rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem c hx),
      div_self (hS z).ne']
end GlobalTheory.PeriodicPartition
