-- Prove2me | solution 1 for GlobalTheory.InertZeta.zVal_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:13.019186+00:00
-- url     : https://prove2.me/submissions/13cb9a8e-3ca9-4a92-b8fa-0094de7d8753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution (q N : ℕ) (X y : ℂ) {r : ℕ} (α : Fin (r + 1) → ℂ) :
    zVal q (N + 2) X y α = (1 - X) * (1 + q * X) * ((1 - y * α 0)⁻¹ * (1 - y / α 0)⁻¹) *
      zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α) := by
  have hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) =
      (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have h : ∀ j ∈ Finset.range N,
        (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
      intro j _; ring
    rw [Finset.prod_congr rfl h]; ring
  have ho : Odd (N + 2) ↔ Odd N := by rw [Nat.odd_add]; simp
  unfold zVal
  rw [hp, Fin.prod_univ_succ, if_congr ho rfl rfl]
  simp only [Fin.tail]
  ring
end GlobalTheory.InertZeta
