-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.pair_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:23.661123+00:00
-- url     : https://prove2.me/submissions/47628fa7-13a2-4a11-be81-6e5afc682d72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_conjT
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_gramQ
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
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) {n : ℕ} {κ μ : Type} (X : Matrix (Fin n ⊕ Fin n) κ L)
    (X' : Matrix (Fin n ⊕ Fin n) μ L) : cT σ (cT σ X * gramQ L n * X') = cT σ X' * gramQ L n * X := by
  simp only [cT_mul, conjT_conjT hσσ, conjT_gramQ, Matrix.mul_assoc]
end GlobalTheory.FrameCompletion
