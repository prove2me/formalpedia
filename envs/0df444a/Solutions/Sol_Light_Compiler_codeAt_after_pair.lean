-- Prove2me | solution 1 for Light.Compiler.codeAt_after_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:23.95653+00:00
-- url     : https://prove2.me/submissions/61b3563f-3789-468f-bff7-64d76753660d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Theorems.Thm_Light_Compiler_length_compileExpr
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}
namespace Light.Compiler
theorem _root_.solution (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, length_compileExpr, length_compileExpr])
end Light.Compiler
