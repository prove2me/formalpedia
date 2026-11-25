-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:02.043664+00:00
-- url     : https://prove2.me/submissions/3884d828-e4de-4d0c-9318-48b5284b2a67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eq_zero_of_eval_skew
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_det_one_add_ne_zero
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_cay_mem_unitary
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_cay_cay
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_denom
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_clearQ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
variable [Fintype ι]
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ),
    (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
      MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) →
    Q = 0 := by
  intro ι _ a Q hQ
  have hR : clearQ Q = 0 := by
    apply eq_zero_of_eval_skew
    intro x hx
    have hAs : ∀ τ, (famOf x τ)ᴴ = -famOf x τ := by
      intro τ; ext i j
      rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
      exact hx (τ, i, j)
    have hdet : ∀ τ, (1 + famOf x τ).det ≠ 0 := fun τ => det_one_add_ne_zero _ (hAs τ)
    have h0 := hQ (fun τ => ⟨cay (famOf x τ), cay_mem_unitary _ (hAs τ)⟩)
    have h0' : eval (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) Q = 0 := h0
    rw [eval_clearQ Q x hdet, h0', zero_mul]
  have hQg : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (1 + g τ).det ≠ 0) →
      eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) Q = 0 := by
    intro g hg
    have hA : ∀ τ, famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ = cay (g τ) :=
      fun τ => Matrix.ext fun i j => rfl
    have hdet : ∀ τ, (1 + famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) τ).det ≠ 0 := by
      intro τ; rw [hA]; exact (cay_cay _ (hg τ)).1
    have h1 := eval_clearQ Q _ hdet
    have hfun : (fun v : ι × Fin a × Fin a =>
        cay (famOf (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) v.1) v.2.1 v.2.2) =
        fun v => g v.1 v.2.1 v.2.2 := by
      funext v; rw [hA, (cay_cay _ (hg v.1)).2]
    rw [hR, map_zero, hfun] at h1
    have hD : eval (fun v : ι × Fin a × Fin a => cay (g v.1) v.2.1 v.2.2) (denom (ι := ι) (a := a)) ≠ 0 := by
      rw [eval_denom]; exact Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
    exact (mul_eq_zero.1 h1.symm).resolve_right (pow_ne_zero _ hD)
  have hprod : Q * denom = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_denom]
    by_cases h : ∀ τ, (1 + famOf x τ).det ≠ 0
    · have : eval x Q = 0 := hQg (famOf x) h
      rw [this, zero_mul]
    · push_neg at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  have hden : (denom (ι := ι) (a := a)) ≠ 0 := by
    intro h
    have := eval_denom (ι := ι) (a := a) (fun _ => 0)
    rw [h, map_zero] at this
    have h1 : ∀ τ, famOf (ι := ι) (a := a) (fun _ => 0) τ = 0 := fun τ => Matrix.ext fun i j => rfl
    simp only [h1, add_zero, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  exact (mul_eq_zero.1 hprod).resolve_right hden
end GlobalTheory.UnitaryZariskiDense
