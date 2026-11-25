-- Prove2me | solution 1 for GlobalTheory.K4.TopW.pow_val_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:20.051901+00:00
-- url     : https://prove2.me/submissions/605bb945-e864-4509-8982-68f23bc2aa93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K4
open GlobalTheory.KEdge GlobalTheory.NeedB
variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
open GlobalTheory.K4.TopW
variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}
namespace GlobalTheory.K4.TopW
theorem _root_.solution [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
end GlobalTheory.K4.TopW
