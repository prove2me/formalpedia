-- Prove2me | solution 1 for GlobalTheory.eq_of_forall_one_tmul_quotient_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:48.591801+00:00
-- url     : https://prove2.me/submissions/53565481-6f69-4072-87ee-f19e82d99f28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_isAdicComplete_of_finite
import Theorems.Thm_GlobalTheory_one_tmul_quotient_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x y : M}
    (h : ∀ n, (1 : R ⧸ I ^ n) ⊗ₜ[R] x = (1 : R ⧸ I ^ n) ⊗ₜ[R] y) : x = y := by
  have := isAdicComplete_of_finite I M
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)
  rw [SModEq.zero, ← one_tmul_quotient_eq_zero_iff, tmul_sub, h, sub_self]
end GlobalTheory
