-- Prove2me | solution 1 for GlobalTheory.ExpPow.pow_exp_I_or_inv_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:49.073321+00:00
-- url     : https://prove2.me/submissions/9ebd5b19-f915-40f9-bbe4-72d8ccae72a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PowExpIOrInvInjective
import Theorems.Thm_GlobalTheory_ExpPow_exp_I_pow_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExpPow
namespace GlobalTheory.ExpPow
theorem _root_.solution :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by
  rintro a b w (rfl | rfl) h
  · exact exp_I_pow_injective a b h
  · rw [inv_pow, inv_pow, inv_inj] at h
    exact exp_I_pow_injective a b h
end GlobalTheory.ExpPow
