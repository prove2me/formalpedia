-- Prove2me | solution 2 for GlobalTheory.T.norm_mul_apply_le_of_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:16.104527+00:00
-- url     : https://prove2.me/submissions/4e1a0f36-dde9-419b-821f-a841e7e12070

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
import Theorems.Thm_GlobalTheory_matrix_mul_entry_norm_le_ultrametric


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
theorem _root_.solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) → ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  first | exact @GlobalTheory.matrix_mul_entry_norm_le_ultrametric | exact GlobalTheory.matrix_mul_entry_norm_le_ultrametric | (intros; apply GlobalTheory.matrix_mul_entry_norm_le_ultrametric <;> assumption)
end _root_.GlobalTheory.T
