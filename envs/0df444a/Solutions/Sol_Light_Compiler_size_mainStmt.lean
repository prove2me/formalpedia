-- Prove2me | solution 1 for Light.Compiler.size_mainStmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:04.125916+00:00
-- url     : https://prove2.me/submissions/eaa91a22-e61d-47e2-9c02-ab2d52b86893

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [mainStmt, Stmt.size, callSize, argsSize, Expr.size]
end Light.Compiler
