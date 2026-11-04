-- Prove2me | solution 1 for Light.Compiler.length_compileStmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:48.232097+00:00
-- url     : https://prove2.me/submissions/eff95229-3c3c-4822-a481-a06773424ce5

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_Light_Compiler_length_compileExpr
import Theorems.Thm_Light_Compiler_length_compileCond
import Theorems.Thm_Light_Compiler_length_argsCode
import Theorems.Thm_Light_Compiler_length_newFrame
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
namespace Light.Compiler
open EndStatement (Instr)
private theorem length_callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) :
    (callCode G p args ret).length = callSize G.F args := by
  simp +arith [callCode, callSize, length_argsCode, length_newFrame]
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
theorem _root_.solution (G : CodeLayout) (s : Stmt) (pos : ℕ) :
    (compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [compileStmt, Stmt.size, length_compileExpr]
  | store a e => simp +arith [compileStmt, Stmt.size, length_compileExpr]
  | seq s t ihs iht => simp [compileStmt, Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [compileStmt, Stmt.size, ihs, iht, length_compileCond]
  | «while» c s ih => simp +arith [compileStmt, Stmt.size, ih, length_compileCond]
  | call p args x => simp [compileStmt, Stmt.size, length_callCode]
end Light.Compiler
