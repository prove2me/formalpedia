-- Prove2me | solution 1 for GlobalTheory.LatticePartition.finite_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:59.284854+00:00
-- url     : https://prove2.me/submissions/aef04d17-6a8a-4ebe-85f9-bddd4de2afd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
namespace GlobalTheory.LatticePartition
theorem _root_.solution {ι : Type} (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (M : ℕ)
    (hS : Summable (fun j => ((1 + a j) ^ M)⁻¹)) (R : ℝ) : {j | a j ≤ R}.Finite := by
  have ht := hS.tendsto_cofinite_zero
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hε : (0 : ℝ) < ((1 + max R 0) ^ M)⁻¹ := by positivity
  have h3 := ht (Iio_mem_nhds hε)
  rw [Filter.mem_map, Filter.mem_cofinite] at h3
  refine h3.subset fun j hj => ?_
  simp only [Set.mem_setOf_eq] at hj
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]
  have hj' : a j ≤ max R 0 := le_trans hj (le_max_left _ _)
  have h0 := ha j
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _)
end GlobalTheory.LatticePartition
