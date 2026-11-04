-- Prove2me | solution 1 for Light.getD_rowMajor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:26.514423+00:00
-- url     : https://prove2.me/submissions/bc1481c1-b08a-4846-95aa-2466b1ab08cb

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast


section
namespace Light
open ThreeSumApsp ThreeSumApsp.WordRam
private theorem rowMajor_succ {n m : ℕ} (A : Fin (n + 1) → Fin m → ℤ) :
    rowMajor A = (List.finRange m).map (A 0) ++ rowMajor fun i : Fin n => A i.succ := by
  simp [rowMajor, List.finRange_succ, List.flatMap_map]
end Light
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m),
    (rowMajor A).getD ((i : ℕ) * m + (j : ℕ)) 0 = A i j
  | 0, _, _, i, _ => i.elim0
  | n + 1, m, A, i, j => by
    rw [rowMajor_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_append_right _ _ _ _ (by simp [Fin.val_succ, Nat.add_mul]; omega)]
      have : ((i'.succ : Fin (n + 1)) : ℕ) * m + (j : ℕ) - ((List.finRange m).map (A 0)).length =
          (i' : ℕ) * m + (j : ℕ) := by
        simp [Fin.val_succ, Nat.add_mul]
        omega
      rw [this]
      exact solution (fun i : Fin n => A i.succ) i' j
end Light
