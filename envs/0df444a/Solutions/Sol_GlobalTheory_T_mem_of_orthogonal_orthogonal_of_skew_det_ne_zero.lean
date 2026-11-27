-- Prove2me | solution 1 for GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:22.765034+00:00
-- url     : https://prove2.me/submissions/4c3824c2-5757-4098-a4ce-3042065352f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeAlt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeStatement
import Theorems.Thm_GlobalTheory_rat_alternating_orthogonal_orthogonal_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq → Mq.det ≠ 0 → ∀ x : Fin r → ℚ, (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  first | exact @GlobalTheory.rat_alternating_orthogonal_orthogonal_le | exact GlobalTheory.rat_alternating_orthogonal_orthogonal_le | (intros; apply GlobalTheory.rat_alternating_orthogonal_orthogonal_le <;> assumption)
end _root_.GlobalTheory.T
