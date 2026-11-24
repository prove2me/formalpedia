-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.rad_mul_levi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:47.934052+00:00
-- url     : https://prove2.me/submissions/64b1bf88-5f6f-4835-83ad-1d8b51f86f67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rcases le_or_gt (β l) (β i) with h1 | h1
    · rw [hu i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
    · rw [hp l j (by omega), mul_zero]
  · simp
end GlobalTheory.CompanionTheory.InertZeta
