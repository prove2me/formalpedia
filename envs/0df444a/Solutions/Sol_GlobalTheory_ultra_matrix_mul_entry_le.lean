-- Prove2me | solution 1 for GlobalTheory.ultra_matrix_mul_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:52.869859+00:00
-- url     : https://prove2.me/submissions/e673d34e-3459-450f-924a-03356bd35759

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E] {n : Type} [Fintype n]
    [DecidableEq n] (A B : Matrix n n E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
end GlobalTheory
