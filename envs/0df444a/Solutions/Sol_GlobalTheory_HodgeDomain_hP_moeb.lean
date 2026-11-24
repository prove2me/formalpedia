-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hP_moeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:38.486369+00:00
-- url     : https://prove2.me/submissions/58c8504e-41bc-4f2e-a78d-f50c6319534c

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_upq_right
import Theorems.Thm_GlobalTheory_HodgeDomain_moeb_mul_kapQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.HodgeDomain
variable {p q : ℕ}
private lemma fromCols_mul_Jpq {m : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ) :
    fromCols A B * Jpq p q = fromCols A (-B) := by
  ext i (j | j) <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
private lemma fromCols_mul_Jpq_mul_conjTranspose_fromCols {m n : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ)
    (C : Matrix n (Fin p) ℂ) (D : Matrix n (Fin q) ℂ) :
    fromCols A B * Jpq p q * (fromCols C D)ᴴ = A * Cᴴ - B * Dᴴ := by
  rw [fromCols_mul_Jpq]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]
private lemma fromCols_mul_eq_blocks {m : Type*} (X : Matrix m (Fin p) ℂ) (Y : Matrix m (Fin q) ℂ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    fromCols X Y * M = fromCols (X * M.toBlocks₁₁ + Y * M.toBlocks₂₁) (X * M.toBlocks₁₂ + Y * M.toBlocks₂₂) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
private lemma mul_fromCols' {m k : Type*} [Fintype m] (N : Matrix k m ℂ) (X : Matrix m (Fin p) ℂ)
    (Y : Matrix m (Fin q) ℂ) : N * fromCols X Y = fromCols (N * X) (N * Y) := by
  ext i (j | j) <;> simp [Matrix.mul_apply]
example (c : ℝ) : hodge c (0 : Matrix (Fin p) (Fin q) ℂ) = (c : ℂ) • 1 := by
  simp [hodge, blkMet, hP, hQ, ← fromBlocks_one, fromBlocks_smul]
end GlobalTheory.HodgeDomain
end
end

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HodgeDomain
variable {p q : ℕ}
namespace GlobalTheory.HodgeDomain
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    jW g z * hP z * (jW g z)ᴴ = hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) := by
  have h := upq_right hg
  have e := moeb_mul_kapQ hg hz
  unfold jW hP
  unfold kapQ at e
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h e ⊢
  generalize moeb G z = w at e ⊢
  rw [Matrix.mul_add, ← Matrix.mul_assoc] at e
  have k1 : fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G =
      (G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) := by
    rw [fromCols_mul_eq_blocks, mul_fromCols']
    have b1 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₁ + -w * G.toBlocks₂₁ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * 1 := by
      rw [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, sub_eq_add_neg]
    have b2 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₂ + -w * G.toBlocks₂₂ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * -z := by
      rw [Matrix.one_mul, Matrix.neg_mul, eq_sub_of_add_eq' e, Matrix.mul_neg, Matrix.sub_mul]
      abel
    rw [b1, b2]
  have k2 : (G.toBlocks₁₁ - w * G.toBlocks₂₁) *
        (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ) *
        (G.toBlocks₁₁ - w * G.toBlocks₂₁)ᴴ =
      fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w))ᴴ := by
    calc _ = ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z)) * Jpq p q *
          ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G)ᴴ := by
            rw [k1]
      _ = _ := by
            rw [conjTranspose_mul]
            conv_rhs => rw [← h]
            simp only [Matrix.mul_assoc]
  rw [fromCols_mul_Jpq_mul_conjTranspose_fromCols, fromCols_mul_Jpq_mul_conjTranspose_fromCols] at k2
  simpa only [conjTranspose_one, Matrix.mul_one, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using k2
end GlobalTheory.HodgeDomain
