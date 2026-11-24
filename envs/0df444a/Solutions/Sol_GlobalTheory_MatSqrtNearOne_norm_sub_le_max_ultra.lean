-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.norm_sub_le_max_ultra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:18.698241+00:00
-- url     : https://prove2.me/submissions/af96f00b-bd73-441c-8403-b6dc7c8fec54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_add_le_max_ultra

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [sub_eq_add_neg, ← norm_neg B]
  exact norm_add_le_max_ultra A (-B)
end GlobalTheory.MatSqrtNearOne
