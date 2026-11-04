-- Prove2me | solution 1 for Light.Compiler.length_newFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:59.326604+00:00
-- url     : https://prove2.me/submissions/ecbed917-568a-47e1-9a42-7c24caec5d1b

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
namespace Light.Compiler
open EndStatement (Instr)
private theorem length_frameInit (F n : ℕ) : (frameInit F n).length = 2 * F := by
  simp [frameInit, List.length_flatMap, Nat.mul_comm]
end Compiler
section width
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
end width
end Light
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (F n ret : ℕ) : (newFrame F n ret).length = 2 * F + 4 := by
  simp +arith [newFrame, length_frameInit]
end Light.Compiler
