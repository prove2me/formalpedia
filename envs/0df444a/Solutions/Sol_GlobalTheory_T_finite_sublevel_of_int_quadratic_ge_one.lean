-- Prove2me | solution 1 for GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:29.472814+00:00
-- url     : https://prove2.me/submissions/7ccb4687-baa0-450d-915b-261a94210133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSublevelOfIntQuadraticGeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSublevelOfIntQuadraticGeOneStatement
import Theorems.Thm_GlobalTheory_posquad_finite


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  first | exact @GlobalTheory.posquad_finite | exact GlobalTheory.posquad_finite | (intros; apply GlobalTheory.posquad_finite <;> assumption)
end _root_.GlobalTheory.T
