-- Prove2me | solution 1 for GlobalTheory.T.ultrametric_matrix_inv_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:13.71595+00:00
-- url     : https://prove2.me/submissions/b82c9e4c-3510-4a31-abd2-75b8ea1fbe1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOneStatement
import Theorems.Thm_GlobalTheory_matrix_inv_near_one


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
theorem _root_.solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 → (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  first | exact @GlobalTheory.matrix_inv_near_one | exact GlobalTheory.matrix_inv_near_one | (intros; apply GlobalTheory.matrix_inv_near_one <;> assumption)
end _root_.GlobalTheory.T
