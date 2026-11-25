-- Prove2me | solution 1 for GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:45:56.464807+00:00
-- url     : https://prove2.me/submissions/9aef9e30-0b8e-47a4-abe5-40e372965aba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiplesStatement
import Theorems.Thm_P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  first | exact @GlobalTheory.card_zmod_tensor_eq_card_quot' | exact GlobalTheory.card_zmod_tensor_eq_card_quot' | (intros; apply GlobalTheory.card_zmod_tensor_eq_card_quot' <;> assumption)
end _root_.GlobalTheory.T
