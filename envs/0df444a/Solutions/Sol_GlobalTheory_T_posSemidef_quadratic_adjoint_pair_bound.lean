-- Prove2me | solution 1 for GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:29.53543+00:00
-- url     : https://prove2.me/submissions/a8047384-7098-41b6-ac1f-675b253539fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosSemidefQuadraticAdjointPairBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosSemidefQuadraticAdjointPairBoundStatement
import Theorems.Thm_GlobalTheory_PosFormAdjoint_pos_form_adjoint_bound


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y := by
  first | exact @GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | exact GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | (intros; apply GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound <;> assumption)
end _root_.GlobalTheory.T
