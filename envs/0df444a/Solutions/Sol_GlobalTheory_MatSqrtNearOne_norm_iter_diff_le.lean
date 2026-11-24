-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.norm_iter_diff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:03.30481+00:00
-- url     : https://prove2.me/submissions/d71444a5-a7d6-4d0a-9517-d10593eeb5db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_mul_le_ultra
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_add_le_max_ultra
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_commute_iter
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_iter_le
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_matrix_sub_mul_self_sub_eq_neg_mul_of_commute

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
theorem _root_.solution {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k
  | 0 => by simp [iter]
  | k + 1 => by
    have hcomm : Commute (iter u k) (iter u (k + 1)) :=
      commute_iter (commute_iter (Commute.refl u) k).symm (k + 1)
    show ‖(u - iter u (k + 1) * iter u (k + 1)) - (u - iter u k * iter u k)‖ ≤ _
    rw [matrix_sub_mul_self_sub_eq_neg_mul_of_commute u _ _ hcomm, norm_neg]
    have hab : ‖iter u k + iter u (k + 1)‖ ≤ ‖u‖ :=
      (norm_add_le_max_ultra _ _).trans (max_le (norm_iter_le hc k) (norm_iter_le hc (k + 1)))
    calc ‖(iter u (k + 1) - iter u k) * (iter u k + iter u (k + 1))‖
        ≤ ‖iter u (k + 1) - iter u k‖ * ‖iter u k + iter u (k + 1)‖ := norm_mul_le_ultra _ _
      _ ≤ (‖u‖ * ‖u‖ ^ k) * ‖u‖ :=
          mul_le_mul (solution hc k) hab (norm_nonneg _) (by positivity)
      _ = ‖u‖ * ‖u‖ ^ (k + 1) := by ring
end GlobalTheory.MatSqrtNearOne
