-- Prove2me | solution 1 for Light.Compiler.codeAt_tailCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:13.153219+00:00
-- url     : https://prove2.me/submissions/fcf89091-37cb-417e-8807-439ad91620cd

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_Light_Compiler_size_mainStmt
import Theorems.Thm_Light_Compiler_length_compileStmt
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_codeAt_self
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


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
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) :=
  (codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [length_compileStmt, size_mainStmt, tailPos, codeLayout])
end Light.Compiler
