-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.exp_inv_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:04:38.634422+00:00
-- url     : https://prove2.me/submissions/a3783f0c-a4f5-4fcb-b111-8d19f69d9bad

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
    (WithZero.exp (n : ℤ))⁻¹ * x ≤ WithZero.exp (e : ℤ) ↔ x ≤ WithZero.exp ((n + e : ℕ) : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero, zero_le']
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    push_cast
    omega
end GlobalTheory.CompanionTheory.InertLen
