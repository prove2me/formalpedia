-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.kapQ_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:25.09215+00:00
-- url     : https://prove2.me/submissions/1b870e2f-702a-40fb-8765-a0103bdb1e29

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_upq_iff
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
private lemma Jpq_mul_fromRows {n : Type*} (C : Matrix (Fin p) n ℂ) (D : Matrix (Fin q) n ℂ) :
    Jpq p q * fromRows C D = fromRows C (-D) := by
  ext (i | i) j <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
private lemma conjTranspose_fromRows_mul_Jpq_mul_fromRows {n m : Type*} (A : Matrix (Fin p) n ℂ) (B : Matrix (Fin q) n ℂ)
    (C : Matrix (Fin p) m ℂ) (D : Matrix (Fin q) m ℂ) :
    (fromRows A B)ᴴ * Jpq p q * fromRows C D = Aᴴ * C - Bᴴ * D := by
  rw [Matrix.mul_assoc, Jpq_mul_fromRows]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]
private lemma blocks_mul_fromRows {n : Type*} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (X : Matrix (Fin p) n ℂ) (Y : Matrix (Fin q) n ℂ) :
    M * fromRows X Y = fromRows (M.toBlocks₁₁ * X + M.toBlocks₁₂ * Y) (M.toBlocks₂₁ * X + M.toBlocks₂₂ * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
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
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) (z : Matrix (Fin p) (Fin q) ℂ) :
    (kapQ g z)ᴴ * kapQ g z -
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂)ᴴ *
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) = hQ z := by
  have h := upq_iff.mp hg
  unfold kapQ hQ
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have e1 : (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ) := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
  rw [blocks_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows] at e1
  simp only [Matrix.mul_one, conjTranspose_one] at e1
  simpa only [neg_sub] using congrArg Neg.neg e1
end GlobalTheory.HodgeDomain
