-- Prove2me | solution 1 for Light.Compiler.codeAt_mainStmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:37.118707+00:00
-- url     : https://prove2.me/submissions/4cd3f039-70c1-45c1-ae73-e484728e2f4a

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_codeAt_self

section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
section parts
variable (P : Program) (p0 : ℕ) (dec : Bool)
private theorem codeAt_mainCode : CodeAt (compileProgram P p0 dec) mainPos (mainCode P p0 dec) :=
  (codeAt_self _).left.left.left.right
end parts
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)
namespace Light.Compiler
theorem _root_.solution :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) :=
  (codeAt_mainCode P p0 dec).left
end Light.Compiler
