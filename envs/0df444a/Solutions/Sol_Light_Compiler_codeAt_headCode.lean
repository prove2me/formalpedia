-- Prove2me | solution 1 for Light.Compiler.codeAt_headCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:35.928408+00:00
-- url     : https://prove2.me/submissions/a7e4024d-f555-4c0e-8b7b-566a2bfa414f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_codeAt_self


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)
namespace Light.Compiler
theorem _root_.solution : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) :=
  (codeAt_self _).left.left.left.left
end Light.Compiler
