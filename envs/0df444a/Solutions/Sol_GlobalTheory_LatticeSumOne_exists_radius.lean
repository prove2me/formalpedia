-- Prove2me | solution 1 for GlobalTheory.LatticeSumOne.exists_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:40:03.91702+00:00
-- url     : https://prove2.me/submissions/a257ffa8-d1ef-49c8-916d-736674424c0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLattice
import Theorems.Thm_GlobalTheory_PeriodicPartition_exists_finite_subcover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.LatticeSumOne
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.LatticeSumOne
theorem _root_.solution (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ R : ℝ, ∀ x : V, ∃ l : Λ, ‖x + l‖ ≤ R := by
  obtain ⟨t, ht⟩ := GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun k : V => {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1})
    (fun k => by
      have : {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1} =
          ⋃ l : Λ, (fun z : V => z + l) ⁻¹' Metric.ball k 1 := by
        ext z; simp
      rw [this]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (by fun_prop))
    (fun k l z hz => by
      obtain ⟨m, hm⟩ := hz
      refine ⟨m - l, ?_⟩
      simpa [add_sub_cancel, add_assoc, sub_eq_add_neg] using hm)
    (fun z => ⟨z, 0, by simp⟩)
  refine ⟨1 + ∑ k ∈ t, ‖k‖, fun x => ?_⟩
  obtain ⟨k, hk, l, hl⟩ := ht x
  refine ⟨l, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hl
  have h1 : ‖k‖ ≤ ∑ k ∈ t, ‖k‖ := Finset.single_le_sum (f := fun k => ‖k‖) (fun _ _ => norm_nonneg _) hk
  calc ‖x + l‖ = ‖(x + l - k) + k‖ := by abel_nf
    _ ≤ ‖x + l - k‖ + ‖k‖ := norm_add_le _ _
    _ ≤ 1 + ∑ k ∈ t, ‖k‖ := by linarith
end GlobalTheory.LatticeSumOne
