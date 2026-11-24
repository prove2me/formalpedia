-- Prove2me | solution 1 for GlobalTheory.PrinTwo.ev_bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:31.475133+00:00
-- url     : https://prove2.me/submissions/a1a084c7-107c-4ace-8ef8-8010f18a281a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_bor_mem_parab
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_wE
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) (g : GL (Fin (1 + 1)) k) :
    ev f (bor a d x * g) = bchar μ₁ μ₂ a d * ev f g := by
  have h := f.1.2 ⟨_, bor_mem_parab a d x⟩ g
  simp only [ev]
  rw [show (bor a d x * g) = ((⟨_, bor_mem_parab a d x⟩ : parab k _) : GL (Fin (1 + 1)) k) * g from rfl, h]
  generalize f.1.1 g = v
  set p : parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := ⟨_, bor_mem_parab a d x⟩
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  have e1 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p false) = a := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩) = a
    rw [two_false, Subsingleton.elim (default : Fin 1) 0, h0, val_bor]
    rfl
  have e2 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p true) = d := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩) = d
    rw [two_true, Subsingleton.elim (default : Fin 1) 0, h1, val_bor]
    rfl
  have hd : (deltaHalf k (Two (Fin 1) (Fin 1)) (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p) : ℂ) =
      ((absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ) := by
    rw [← MulEquiv.apply_symm_apply (leviTwo k (Fin 1) (Fin 1)) (leviProj k _ p), deltaHalf_two]
    simp only [Fintype.card_fin, Nat.cast_one]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl, e1, e2]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul y z =>
    show TensorProduct.lid ℂ ℂ ((deltaHalf k _ (leviProj k _ p) : ℂ) • extTensor (detRep (Fin 1) μ₁)
      (detRep (Fin 1) μ₂) ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)) (y ⊗ₜ z)) = _
    rw [extTensor_tmul, hd]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl]
    simp only [detRep, ofChar_apply, detChar_apply, e1, e2, map_smul, TensorProduct.lid_tmul, bchar,
      Units.val_mul, smul_eq_mul]
    ring
  | add y z hy hz =>
    rw [map_add, map_add, map_add, hy, hz, mul_add]
end GlobalTheory.PrinTwo
