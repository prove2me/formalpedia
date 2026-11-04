-- Prove2me | solution 1 for Light.Compiler.cStack_succ_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:59.318486+00:00
-- url     : https://prove2.me/submissions/581e32ed-69de-4a54-b3c7-61849a5a13b3

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_Light_Compiler_cStack_add

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := cStack_add q 1
end Light.Compiler
