-- Prove2me | solution 1 for GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:14.911996+00:00
-- url     : https://prove2.me/submissions/8137008c-13c5-4a47-94f1-4795a4fd63ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScaling
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScalingStatement
import Theorems.Thm_GlobalTheory_DI_cartierAt_signFactorial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E) (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) → (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  first | exact @GlobalTheory.DI.cartierAt_signFactorial | exact GlobalTheory.DI.cartierAt_signFactorial | (intros; apply GlobalTheory.DI.cartierAt_signFactorial <;> assumption)
end _root_.GlobalTheory.T
