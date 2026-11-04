-- Prove2me | solution 1 for Light.Compiler.length_compileCond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:57.10779+00:00
-- url     : https://prove2.me/submissions/25338b95-d83d-4511-8ae0-174e3f81e213

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_Light_Compiler_length_compileExpr
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (c : Cond) (l : ℕ) : (compileCond c l).length = c.size := by
  cases c <;> simp +arith [compileCond, Cond.size, length_compileExpr]
end Light.Compiler
