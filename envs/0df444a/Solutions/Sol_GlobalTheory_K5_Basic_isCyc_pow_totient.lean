-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isCyc_pow_totient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:56.260381+00:00
-- url     : https://prove2.me/submissions/f201f4fb-995f-451e-b026-f160afb23dba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isCyc_mul
import Theorems.Thm_GlobalTheory_K5_Basic_isCyc_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g : Gal p Ω) : χ g ^ Nat.totient (p ^ k) = 1 := by
  have hu : χ g * χ g⁻¹ = 1 := by
    rw [← isCyc_mul h, mul_inv_cancel, isCyc_eq_one_iff h]; rfl
  have := ZMod.pow_totient (Units.mkOfMulEqOne _ _ hu)
  have e := congrArg Units.val this
  rwa [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, Units.val_one] at e
end GlobalTheory.K5.Basic
