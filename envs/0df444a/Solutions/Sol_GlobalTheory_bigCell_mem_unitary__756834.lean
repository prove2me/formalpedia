-- Prove2me | solution 1 for GlobalTheory.bigCell_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:42.226741+00:00
-- url     : https://prove2.me/submissions/9ede3171-1287-4c9c-833c-3a207187adfb

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary
import Theorems.Thm_GlobalTheory_BigCellUnitary_gram_submatrix
import Theorems.Thm_GlobalTheory_BigCellUnitary_bigCell_submatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory
open BigCellUnitary
namespace GlobalTheory
theorem _root_.solution : Formalism.QuantumDeterminants.BigCellMem := by
  intro k r c μ hc hμ
  have key : ((bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ).submatrix (posEquiv k r) (posEquiv k r) =
      (Hpk k r).submatrix (posEquiv k r) (posEquiv k r) := by
    rw [← submatrix_mul_equiv _ _ _ (posEquiv k r), ← submatrix_mul_equiv _ _ _ (posEquiv k r),
      ← conjTranspose_submatrix]
    have hp : ⇑(posEquiv k r) = pos k r := rfl
    rw [hp, gram_submatrix, bigCell_submatrix]
    have h1 : diagonal (fun a => star (c a)) * diagonal (fun a => (star (c a))⁻¹) =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      exact mul_inv_cancel₀ (star_ne_zero.2 (hc a))
    have h2 : diagonal (fun a => star (star (c a))⁻¹) * diagonal c =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      rw [star_inv₀, star_star]
      exact inv_mul_cancel₀ (hc a)
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero, diagonal_conjTranspose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, hμ]
    rw [show star c = fun a => star (c a) from rfl,
      show star (fun a => (star (c a))⁻¹) = fun a => star (star (c a))⁻¹ from rfl, h1, h2]
  ext i j
  obtain ⟨i, rfl⟩ := (posEquiv k r).surjective i
  obtain ⟨j, rfl⟩ := (posEquiv k r).surjective j
  exact congrFun (congrFun key i) j
end GlobalTheory
