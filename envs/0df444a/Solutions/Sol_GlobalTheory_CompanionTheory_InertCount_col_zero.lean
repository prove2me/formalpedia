-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.col_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:04:38.912803+00:00
-- url     : https://prove2.me/submissions/63f72e36-8630-4dc2-a54c-050a2ebb3190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
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
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : colOf w = 0 := by
  have h1 := ((hH L ϖ σ q N hU).1 w hw).1
  funext i
  have h2 := h1 i.rev
  simp only [h0, Pi.zero_apply, Fin.rev_rev, zero_eq_neg] at h2
  exact (map_eq_zero_iff σ σ.injective).mp h2
end GlobalTheory.CompanionTheory.InertCount
