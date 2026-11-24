-- Prove2me | solution 1 for GlobalTheory.Doubling.quot_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:47.757983+00:00
-- url     : https://prove2.me/submissions/dc9823ec-f5ca-40e0-ac9e-647946300cd4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
variable [Fintype n] [Fintype ι]
variable {e}
variable [DecidableEq n] [DecidableEq ι]
variable (e)
namespace GlobalTheory.Doubling
theorem _root_.solution {σ : A →+* A} {J : Matrix n n A} {M : Matrix ι ι A} (hM : cT σ M * dblGram e J * M = dblGram e J)
    (h : KeepsDiag e M) : cT σ (quotMat e M) * J * leviMat e M = J := by
  have h1 : cT σ (M.submatrix e e) * fromBlocks J 0 0 (-J) * M.submatrix e e = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat e, show cT σ (M.submatrix e e) = (cT σ M).submatrix e e from rfl, submatrix_mul_equiv,
      submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e e) hM
  rw [← fromBlocks_toBlocks (M.submatrix e e)] at h1
  simp only [cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  rw [quotMat, cT, Matrix.map_sub _ (map_sub σ), transpose_sub, Matrix.sub_mul, Matrix.sub_mul]
  nth_rewrite 2 [← h]
  rw [leviMat, Matrix.mul_add, Matrix.mul_add]
  refine Eq.trans ?_ ((congrArg₂ (· + ·) h1.1 h1.2.1).trans (add_zero J))
  abel
end GlobalTheory.Doubling
