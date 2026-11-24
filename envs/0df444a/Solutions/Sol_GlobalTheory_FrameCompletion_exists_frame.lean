-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:20:48.787493+00:00
-- url     : https://prove2.me/submissions/29477769-5fcf-45fd-978f-66aa8d8572aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_add
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_fromCols
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_antiJ
import Theorems.Thm_GlobalTheory_FrameCompletion_antiJ_mul_antiJ_mul
import Theorems.Thm_GlobalTheory_FrameCompletion_pair_symm
import Theorems.Thm_GlobalTheory_FrameCompletion_pair_fromRows
import Theorems.Thm_GlobalTheory_FrameCompletion_pair_comb
import Theorems.Thm_GlobalTheory_FrameCompletion_pair_sub
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_smul
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_neg
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_sub
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_conjT
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_fromRows
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_fromCols
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_antiJ
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_gramQ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) (g U V C : Matrix (Fin n) (Fin n) L) (hg : cT σ g * antiJ L n * g = antiJ L n)
    (hUi : IsInt U) (hVi : IsInt V) (hCi : IsInt C) (hDi : IsInt (g * C)) (h5 : (U + V * g) * C = 1) :
    ∃ K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt K ∧ cT σ K * gramQ L n * K = gramQ L n ∧
      ∀ x : Fin n → L, K *ᵥ Sum.elim x x = Sum.elim (C *ᵥ x) ((g * C) *ᵥ x) := by
  set Q := gramQ L n with hQ
  set Y : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows C (g * C) with hY
  set Z : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows (antiJ L n * cT σ U * antiJ L n) (-(antiJ L n * cT σ V * antiJ L n)) with hZ
  have hYY : cT σ Y * Q * Y = 0 := by
    rw [hY, hQ, pair_fromRows, cT_mul,
      show cT σ C * cT σ g * antiJ L n * (g * C) = cT σ C * (cT σ g * antiJ L n * g) * C by simp only [Matrix.mul_assoc], hg, sub_self]
  have hUC : cT σ C * cT σ U + cT σ (g * C) * cT σ V = 1 := by
    rw [← cT_mul, ← cT_mul, ← conjT_add, ← Matrix.mul_assoc V, ← Matrix.add_mul, h5, cT_one]
  have hYZ : cT σ Y * Q * Z = antiJ L n := by
    rw [hY, hZ, hQ, pair_fromRows]
    calc _ = (cT σ C * cT σ U + cT σ (g * C) * cT σ V) * antiJ L n := by
          simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.mul_assoc, antiJ_mul_antiJ_mul]
      _ = antiJ L n := by rw [hUC, Matrix.one_mul]
  have hZY : cT σ Z * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ, conjT_antiJ]
  set H := cT σ Z * Q * Z with hH
  have hHH : cT σ H = H := pair_symm hσσ Z Z
  set Z' := Z - τ • (Y * (antiJ L n * H)) with hZ'
  have hYZ' : cT σ Y * Q * Z' = antiJ L n := by
    rw [hZ', Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hYY, Matrix.zero_mul, smul_zero, sub_zero, hYZ]
  have hZ'Y : cT σ Z' * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ', conjT_antiJ]
  have hZ'Z' : cT σ Z' * Q * Z' = 0 := by
    rw [hZ', pair_sub, hYY, hZY, hYZ, ← hH, cT_mul, hHH, conjT_antiJ, antiJ_mul_antiJ_mul, Matrix.mul_zero,
      Matrix.zero_mul, smul_zero, add_zero, Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.mul_one,
      sub_sub, ← add_smul, hτ1, one_smul, sub_self]
  set a := τ • Y + (1 : L) • Z' with ha
  set b := σ τ • Y + (-1 : L) • Z' with hb
  have hInt : IsInt Y ∧ IsInt Z' := by
    have hYi : IsInt Y := isInt_fromRows hCi hDi
    refine ⟨hYi, isInt_sub (isInt_fromRows ?_ ?_) (isInt_smul hτ (hYi.mul (isInt_antiJ.mul ?_)))⟩
    · exact (isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ
    · exact isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ)
    · have hZi : IsInt Z := isInt_fromRows ((isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ)
        (isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ))
      exact ((isInt_conjT hσ hZi).mul isInt_gramQ).mul hZi
  have hστ : σ τ ∈ intL L := by
    show Valued.v (σ τ) ≤ 1
    rw [hσ]
    exact hτ
  refine ⟨fromCols a b, isInt_fromCols ?_ ?_, ?_, fun x => ?_⟩
  · exact (isInt_smul hτ hInt.1).add (isInt_smul (one_mem _) hInt.2)
  · exact (isInt_smul hστ hInt.1).add (isInt_smul (neg_mem (one_mem _)) hInt.2)
  · rw [conjT_fromCols, fromRows_mul, fromRows_mul_fromCols, ha, hb, pair_comb, pair_comb, pair_comb, pair_comb,
      hYY, hYZ', hZ'Y, hZ'Z', hQ, gramQ]
    simp only [smul_zero, add_zero, zero_add, map_one, map_neg, hσσ, mul_one, one_mul, mul_neg, neg_mul, neg_smul,
      neg_neg]
    rw [← add_smul, add_comm (σ τ), hτ1, one_smul, neg_add_cancel, add_neg_cancel, ← neg_add, ← add_smul, hτ1, one_smul]
  · rw [fromCols_mulVec_sumElim, ← Matrix.add_mulVec, ha, hb,
      show τ • Y + (1 : L) • Z' + (σ τ • Y + (-1 : L) • Z') = (τ + σ τ) • Y by module, hτ1, one_smul, hY,
      fromRows_mulVec]
end GlobalTheory.FrameCompletion
