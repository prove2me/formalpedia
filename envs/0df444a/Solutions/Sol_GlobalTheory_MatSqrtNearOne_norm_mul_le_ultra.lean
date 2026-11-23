-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.norm_mul_le_ultra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:56.942193+00:00
-- url     : https://prove2.me/submissions/5c0d4d29-669f-4805-b9a6-5544db8662b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}
namespace GlobalTheory.MatSqrtNearOne
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_entry_le_entrywise_sup_norm A) (norm_entry_le_entrywise_sup_norm B)
    (norm_nonneg _) (norm_nonneg _)
end GlobalTheory.MatSqrtNearOne
