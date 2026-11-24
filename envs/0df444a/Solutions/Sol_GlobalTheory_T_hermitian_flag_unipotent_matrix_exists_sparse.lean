-- Prove2me | solution 1 for GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:55.661505+00:00
-- url     : https://prove2.me/submissions/bcbeb92b-4739-4238-ad89-84cf4d2dcdc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparse
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparseStatement
import Theorems.Thm_GlobalTheory_isotropic_unipotent_column_relations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  first | exact @GlobalTheory.isotropic_unipotent_column_relations | exact GlobalTheory.isotropic_unipotent_column_relations | (intros; apply GlobalTheory.isotropic_unipotent_column_relations <;> assumption)
end _root_.GlobalTheory.T
