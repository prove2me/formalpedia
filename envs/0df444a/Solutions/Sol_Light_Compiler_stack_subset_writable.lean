-- Prove2me | solution 1 for Light.Compiler.stack_subset_writable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:08.393601+00:00
-- url     : https://prove2.me/submissions/66fccb6c-4833-47d5-acb0-cb998545659d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution {q : ℕ} : Stack q Z.Q ⊆ Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left
end Light.Compiler
