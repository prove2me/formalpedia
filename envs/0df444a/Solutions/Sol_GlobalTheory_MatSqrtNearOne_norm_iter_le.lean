-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.norm_iter_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:23.692+00:00
-- url     : https://prove2.me/submissions/bce38ef2-dc6d-47b7-91ac-48bdafeaa64a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_mul_le_ultra
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_sub_le_max_ultra

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
theorem _root_.solution {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖
  | 0 => by simp [iter]
  | k + 1 => by
    have ih := solution hc k
    refine (norm_sub_le_max_ultra _ _).trans (max_le le_rfl ?_)
    calc ‖iter u k * iter u k‖ ≤ ‖iter u k‖ * ‖iter u k‖ := norm_mul_le_ultra _ _
      _ ≤ ‖u‖ * 1 := mul_le_mul ih (ih.trans hc.le) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u‖ := mul_one _
end GlobalTheory.MatSqrtNearOne
