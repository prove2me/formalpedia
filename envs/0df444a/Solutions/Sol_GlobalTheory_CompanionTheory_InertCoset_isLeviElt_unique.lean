-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.isLeviElt_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:56.585508+00:00
-- url     : https://prove2.me/submissions/dd98f32e-cc7c-4dc9-bce3-562ad27e6ee2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a g m') : m = m' := by
  obtain ⟨hm, h0, hl, hmid⟩ := h
  obtain ⟨hm', h0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := hm'
  have key : ∀ i j, mat m i j = mat m' i j := by
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
      all_goals first
        | (rw [h0, h0'])
        | (rw [hmid, hmid'])
        | (rw [hl, hl'])
        | (simp [blk_zero, blk_mid, blk_last] at hij)
    · rw [hmz i j hij, hmz' i j hij]
  exact Subtype.ext (Units.ext (Matrix.ext key))
end GlobalTheory.CompanionTheory.InertCoset
