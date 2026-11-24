-- Prove2me | solution 1 for GlobalTheory.ColLie.hasDerivAt_coeff_colSub_of_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:34.049427+00:00
-- url     : https://prove2.me/submissions/3e0d1f69-feba-4106-9408-461b147672d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Theorems.Thm_GlobalTheory_ColLie_colDer_mul_X
import Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_coeff_mul_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_ColLie_colDer_X
import Theorems.Thm_GlobalTheory_ColLie_colDer_apply
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
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
namespace GlobalTheory.ColLie
theorem _root_.solution [Fintype ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ)
    (g : ℝ → ι → Matrix (Fin a) (Fin a) ℂ) (h0 : g 0 = 1)
    (hg : ∀ σ i j, HasDerivAt (fun h => g h σ i j) (if σ = τ then S i j else 0) 0)
    (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (g h) R)) (coeff m (colDer τ S R)) 0 := by
  have hone : ∀ P : Pol ι d a, colSub (g 0) P = P := by
    have : (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro y
      rw [h0]
      simp only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single y.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    intro P
    rw [this, AlgHom.id_apply]
  induction R using MvPolynomial.induction_on generalizing m with
  | C c =>
    have h1 : colDer τ S (C c : Pol ι d a) = 0 := by simp [colDer_apply]
    simp only [h1, algHom_C, coeff_zero]
    exact hasDerivAt_const _ _
  | add P Q hP hQ =>
    simp only [map_add, coeff_add]
    exact (hP m).add (hQ m)
  | mul_X P v hP =>
    have e1 : ∀ h, coeff m (colSub (g h) (P * X v)) =
        ∑ k, g h v.1 k v.2.2 * coeff m (colSub (g h) P * X (v.1, v.2.1, k)) := by
      intro h
      rw [map_mul]
      conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by
        simp [colSub]]
      rw [Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, coeff_C_mul]
    simp only [e1]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)
    refine hd.congr_deriv ?_
    rw [colDer_mul_X, coeff_add, Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [h0, Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    · rw [colDer_X, hone]
      by_cases hv : v.1 = τ
      · subst hv
        simp only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]
      · simp [hv]
end GlobalTheory.ColLie
