-- Prove2me | solution 1 for Light.mem_rowMajor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:14.974822+00:00
-- url     : https://prove2.me/submissions/9f6bdf51-5ab0-4804-a16b-895546a1f37d

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {n m : ℕ} {A : Fin n → Fin m → ℤ} {x : ℤ} (h : x ∈ rowMajor A) :
    ∃ i j, A i j = x := by
  simp only [rowMajor, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h
  exact h
end Light
