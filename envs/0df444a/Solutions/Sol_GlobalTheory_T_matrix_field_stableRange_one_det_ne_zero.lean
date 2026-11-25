-- Prove2me | solution 1 for GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:51.555568+00:00
-- url     : https://prove2.me/submissions/6b4f8980-dbb0-4a71-b52b-c754b9ec87ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixFieldStableRangeOneDetNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixFieldStableRangeOneDetNeZeroStatement
import Theorems.Thm_P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab


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
theorem _root_.solution : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ), c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  first | exact @GlobalTheory.matrix_stableRange_one' | exact GlobalTheory.matrix_stableRange_one' | (intros; apply GlobalTheory.matrix_stableRange_one' <;> assumption)
end _root_.GlobalTheory.T
