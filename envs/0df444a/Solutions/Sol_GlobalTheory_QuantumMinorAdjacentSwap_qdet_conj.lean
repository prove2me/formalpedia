-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:02.534256+00:00
-- url     : https://prove2.me/submissions/5fee58fb-7c35-4ff2-b952-73eb1b8987de

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_prod_ofFn_sum_smul
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_cast_sign_mul
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_qminor_comp_perm
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_qminor_eq_zero
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_sum_eq_sum_perm
import Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_Tm_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) :
    qdet (fun (a b : Fin n) ↦ ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) u
      = qdet E u := by
  have hrow : ∀ d : Fin n → Fin n,
      ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => ∑ c, P c (σ k) • Tm E (u - (k : ℂ)) c (d k)).prod =
      P.det • qminor E id d u := by
    intro d
    simp only [prod_ofFn_sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hdet : ∀ c : Fin n → Fin n,
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ k, P (c k) (σ k) =
          (P.submatrix c id).det := by
      intro c
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    simp only [hdet]
    rw [sum_eq_sum_perm]
    · simp only [qminor, cast_sign_mul, Finset.smul_sum, smul_smul, Matrix.det_permute, id,
        mul_comm]
    · intro c hc
      obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hc
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), zero_smul]
  have h1 : qdet (fun (a b : Fin n) ↦ ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) u =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • P.det • qminor E id d u := by
    simp only [← hrow, Finset.smul_sum]
    rw [Finset.sum_comm]
    unfold qdet qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [id, Tm_conj E P Q h, cast_sign_mul]
    rw [prod_ofFn_sum_smul (fun k d => Q k d)
      (fun k d => ∑ c, P c (σ k) • Tm E (u - ((k : Fin n) : ℂ)) c d), Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _
  rw [h1, sum_eq_sum_perm]
  · have h2 : ∀ σ : Equiv.Perm (Fin n), qminor E id σ u =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • qdet E u := fun σ =>
      qminor_comp_perm E hE id u σ id
    simp only [h2, smul_smul, ← Finset.sum_smul]
    have h3 : ∑ σ : Equiv.Perm (Fin n),
        (∏ k, Q k (σ k)) * (P.det * (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) = Q.det * P.det := by
      rw [← Matrix.det_transpose Q, Matrix.det_apply' Q.transpose, Finset.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [Matrix.transpose_apply]
      ring
    rw [h3, ← Matrix.det_mul, h, Matrix.det_one, one_smul]
  · intro d hd
    rw [qminor_eq_zero E hE id u d hd, smul_zero, smul_zero]
end GlobalTheory.QuantumMinorAdjacentSwap
