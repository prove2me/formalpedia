-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:08.348008+00:00
-- url     : https://prove2.me/submissions/75e70f70-295c-4101-ac6a-eb7d248dfe20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMemStatement
import Theorems.Thm_GlobalTheory_CentralIdemIntegral_card_mul_coeff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  first | exact @GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | exact GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | (intros; apply GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem <;> assumption)
end _root_.GlobalTheory.T
