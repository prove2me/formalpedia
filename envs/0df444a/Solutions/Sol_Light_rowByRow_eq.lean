-- Prove2me | solution 1 for Light.rowByRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:21.235023+00:00
-- url     : https://prove2.me/submissions/29c2a71b-b175-41d9-a149-6d81ec2ef9f9

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
theorem _root_.solution {n : ℕ} (w : Fin n → Fin n → ℤ) : EndStatement.rowByRow w = rowMajor w := by
  simp [EndStatement.rowByRow, rowMajor, List.ofFn_eq_map, List.flatMap_def]
end Light
