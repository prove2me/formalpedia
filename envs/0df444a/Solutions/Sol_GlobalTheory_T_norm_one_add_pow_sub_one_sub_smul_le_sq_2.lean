-- Prove2me | solution 2 for GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:32.299838+00:00
-- url     : https://prove2.me/submissions/a5510395-b7b6-41f4-a58a-8ee6cb35645d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLeStatement
import Theorems.Thm_GlobalTheory_matrix_one_add_pow_sub_entry_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) → ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  first | exact @GlobalTheory.matrix_one_add_pow_sub_entry_le | exact GlobalTheory.matrix_one_add_pow_sub_entry_le | (intros; apply GlobalTheory.matrix_one_add_pow_sub_entry_le <;> assumption)
end _root_.GlobalTheory.T
