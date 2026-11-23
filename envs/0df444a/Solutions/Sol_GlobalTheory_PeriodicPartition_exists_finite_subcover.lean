-- Prove2me | solution 1 for GlobalTheory.PeriodicPartition.exists_finite_subcover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:03.825103+00:00
-- url     : https://prove2.me/submissions/393dc95f-5ecb-43e6-a985-b1364b02f56b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity

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
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Manifold
open scoped Pointwise
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory.PeriodicPartition
namespace _root_.GlobalTheory.PeriodicPartition
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {κ : Type} (V : κ → Set E) (hV : ∀ k, IsOpen (V k))
    (hper : ∀ k (l : Λ) z, z ∈ V k → z + l ∈ V k) (hcov : ∀ z, ∃ k, z ∈ V k) :
    ∃ t : Finset κ, ∀ z, ∃ k ∈ t, z ∈ V k := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b')) :=
    (ZSpan.fundamentalDomain_isBounded b').isCompact_closure
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (fun z _ => Set.mem_iUnion.2 (hcov z))
  refine ⟨t, fun z => ?_⟩
  obtain ⟨k, hk, hz⟩ := Set.mem_iUnion₂.1 (ht (subset_closure (ZSpan.fract_mem_fundamentalDomain b' z)))
  have hmem : (ZSpan.floor b' z : E) ∈ Λ := by
    exact (b.ofZLatticeBasis_span ℝ Λ).le (ZSpan.floor b' z).2
  refine ⟨k, hk, ?_⟩
  simpa [ZSpan.fract_apply] using hper k ⟨_, hmem⟩ _ hz
end _root_.GlobalTheory.PeriodicPartition
end GlobalTheory.PeriodicPartition
