-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCorner.H_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:22:13.658412+00:00
-- url     : https://prove2.me/submissions/ad4f160e-ad71-4453-8a83-011dc86d6c6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertCorner
theorem _root_.solution {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin N) (Fin N) L} (hA : IsInt A)
    {x : Fin N → L} (hx : ∀ j, x j ∈ intL L) : H σ x A x ∈ intL L := by
  have hs : ∀ a, a ∈ intL L → σ a ∈ intL L := by
    intro a ha
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at ha ⊢
    rw [hv]
    exact ha
  simp only [H, dotProduct, Matrix.mulVec, dv]
  exact Subring.sum_mem _ (fun i _ => Subring.mul_mem _ (hx i)
    (Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hA i k) (hs _ (hx _)))))
end GlobalTheory.CompanionTheory.InertCorner
