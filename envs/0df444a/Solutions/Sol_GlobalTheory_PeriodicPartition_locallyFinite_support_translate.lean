-- Prove2me | solution 1 for GlobalTheory.PeriodicPartition.locallyFinite_support_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:04.173424+00:00
-- url     : https://prove2.me/submissions/cdfd4941-75aa-49ab-9376-849dc6269dd7

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
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) :
    LocallyFinite fun l : Λ => Function.support fun z : E => φ (z + l) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hclosed : IsClosed (Λ : Set E) :=
    AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
  have hfin : ((tsupport φ - Metric.closedBall x 1) ∩ (Λ : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hφ.isBounded.sub Metric.isBounded_closedBall) hclosed
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro l ⟨z, hz, hzb⟩
  refine ⟨?_, l.2⟩
  have hmem := Set.sub_mem_sub (subset_tsupport φ (show z + (l : E) ∈ Function.support φ from hz)) hzb
  rwa [add_sub_cancel_left] at hmem
end _root_.GlobalTheory.PeriodicPartition
end GlobalTheory.PeriodicPartition
