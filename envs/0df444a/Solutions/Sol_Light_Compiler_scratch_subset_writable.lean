-- Prove2me | solution 1 for Light.Compiler.scratch_subset_writable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:45.76337+00:00
-- url     : https://prove2.me/submissions/42df7360-b41f-4860-af3f-fc07ae82c8cc

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
theorem _root_.solution {q : ℕ} : Scratch Z.F ⊆ Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left
end Light.Compiler
