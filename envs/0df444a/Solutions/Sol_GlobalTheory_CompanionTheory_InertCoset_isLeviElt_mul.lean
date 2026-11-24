-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.isLeviElt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:22:12.38716+00:00
-- url     : https://prove2.me/submissions/2a9b2430-d281-47b5-954e-0866bb99d469

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution (h0 : ϖ ≠ 0) (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a' g' m') :
    IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  obtain ⟨hm, hm0, hl, hmid⟩ := h
  obtain ⟨hm', hm0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmat : mat (m * m') = mat m * mat m' := rfl
  refine ⟨Subgroup.mul_mem _ hm hm', ?_, ?_, ?_⟩
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz 0 (mid j) (by simp [blk_zero, blk_mid]), zero_mul]),
      hmz 0 (Fin.last (N + 1)) (by simp [blk_zero, blk_last]), hm0, hm0', zpow_add₀ h0]
    ring
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz (Fin.last (N + 1)) (mid j) (by simp [blk_last, blk_mid]), zero_mul]),
      hmz (Fin.last (N + 1)) 0 (by simp [blk_zero, blk_last]), hl, hl', neg_add, zpow_add₀ h0]
    ring
  · intro i j
    rw [hmat, Matrix.mul_apply, sum_idx, hmz (mid i) 0 (by simp [blk_zero, blk_mid]),
      hmz (mid i) (Fin.last (N + 1)) (by simp [blk_mid, blk_last])]
    simp only [zero_mul, zero_add, add_zero, hmid, hmid']
    show _ = (mat g * mat g') i j
    rw [Matrix.mul_apply]
end GlobalTheory.CompanionTheory.InertCoset
