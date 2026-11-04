-- Prove2me | solution 1 for Light.mem_rowMajor_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:16.134656+00:00
-- url     : https://prove2.me/submissions/13becaf2-bb2c-4813-b79d-8041ed748033

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
theorem _root_.solution {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m) :
    A i j ∈ rowMajor A := by
  simp only [rowMajor, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, j, rfl⟩
end Light
