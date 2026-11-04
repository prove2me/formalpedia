-- Prove2me | solution 1 for Light.length_rowMajor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:25.12743+00:00
-- url     : https://prove2.me/submissions/8f643c87-1e93-435f-94da-535aea4f56ef

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
theorem _root_.solution : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ), (rowMajor A).length = n * m
  | 0, m, A => by simp [rowMajor]
  | n + 1, m, A => by
    rw [rowMajor_succ, List.length_append, solution, List.length_map, List.length_finRange]
    ring
end Light
