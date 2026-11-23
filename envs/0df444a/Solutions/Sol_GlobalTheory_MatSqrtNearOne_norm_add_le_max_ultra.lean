-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.norm_add_le_max_ultra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:36.888013+00:00
-- url     : https://prove2.me/submissions/ee22afc3-32f7-4ac2-92f7-99512fc58dcf

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [Matrix.norm_le_iff (le_max_of_le_left (norm_nonneg _))]
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_entry_le_entrywise_sup_norm A) (norm_entry_le_entrywise_sup_norm B))
end GlobalTheory.MatSqrtNearOne
