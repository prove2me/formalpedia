-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.exp_inv_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:53.735801+00:00
-- url     : https://prove2.me/submissions/8eca8722-a843-4d50-92cb-7f8e199d2c03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution (n e : ℕ) (x : WithZero (Multiplicative ℤ)) :
    (WithZero.exp (n : ℤ))⁻¹ * x = WithZero.exp (e : ℤ) ↔ x = WithZero.exp ((n + e : ℕ) : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero]
    constructor <;> intro h
    · exact absurd h.symm WithZero.exp_ne_zero
    · exact absurd h.symm WithZero.exp_ne_zero
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj, WithZero.exp_inj]
    push_cast
    omega
end GlobalTheory.CompanionTheory.InertLen
