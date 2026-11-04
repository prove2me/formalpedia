-- Prove2me | solution 1 for Light.Compiler.length_argsCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:58.20567+00:00
-- url     : https://prove2.me/submissions/5ce01fec-c078-4817-8eee-d15fb123b427

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
theorem _root_.solution (es : List Expr) (k : ℕ) : (argsCode es k).length = argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [argsCode, argsSize, length_compileExpr, ih]
end Light.Compiler
