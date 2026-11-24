-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.levi_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:28.854586+00:00
-- url     : https://prove2.me/submissions/cae50424-b71c-42fc-afa2-2abdcf1d21b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_off
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) (hg : IsBorelU g) :
    IsBorelU m := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at hij
  · simp at hij
  · simp at hij
  · exact o2 _
  · exact (h.2.2.2 i j).trans (hg i j (by
      have h' : j.val + 1 < i.val + 1 := hij
      exact Fin.lt_def.2 (by omega)))
  · exact absurd hij (not_lt.2 (Fin.le_last _))
  · exact o4
  · exact o6 _
  · exact absurd hij (lt_irrefl _)
end GlobalTheory.CompanionTheory.InertTrans
