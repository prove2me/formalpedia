-- Prove2me | solution 1 for Light.matAt_of_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:20.057335+00:00
-- url     : https://prove2.me/submissions/78574c2f-8e67-4353-862e-243b55d0d2f3

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Theorems.Thm_Light_length_rowMajor
import Theorems.Thm_Light_getD_rowMajor
import Theorems.Thm_Nat_mul_add_lt_mul


set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {n k : ℕ} {μ : ℕ → ℤ} {a : ℕ} {A : Matrix (Fin n) (Fin k) ℤ}
    (h : Seg μ a (rowMajor A)) : MatAt μ a A := by
  intro i j
  have hlt : (i : ℕ) * k + (j : ℕ) < (rowMajor A).length :=
    (Nat.mul_add_lt_mul i.isLt j.isLt).trans_eq (length_rowMajor _).symm
  rw [Nat.add_assoc, h _ hlt, ← List.getD_eq_getElem _ 0 hlt]
  exact getD_rowMajor A i j
end Light
