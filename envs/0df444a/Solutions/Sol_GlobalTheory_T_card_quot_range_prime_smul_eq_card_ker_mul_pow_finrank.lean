-- Prove2me | solution 1 for GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:43.285883+00:00
-- url     : https://prove2.me/submissions/53a97ab6-ff6a-4c7a-90dc-cac28ce5e290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
import Theorems.Thm_GlobalTheory_card_quot_prime_smul_eq_card_ker_mul_pow_finrank


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
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by
  first | exact @GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | exact GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | (intros; apply GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank <;> assumption)
end _root_.GlobalTheory.T
