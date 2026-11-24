-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.levi_mul_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:34.413633+00:00
-- url     : https://prove2.me/submissions/34fffb06-10bf-4471-8ade-bf5c40087a14

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
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
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
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) :
    mat (x * y) (Fin.last (N + 1)) (Fin.last (N + 1)) =
      mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * mat y (Fin.last (N + 1)) (Fin.last (N + 1)) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
    zero_add]
  intro j _
  rw [hx (Fin.last (N + 1)) (mid j) (by simp), zero_mul]
end GlobalTheory.CompanionTheory.InertZeta
