-- Prove2me | solution 1 for Light.Compiler.length_compileExpr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:45.732942+00:00
-- url     : https://prove2.me/submissions/f514f619-55a2-44a9-a4d3-60b5e1b9ee2c

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
private theorem length_digitsCode (c : ℤ) (L : List ℕ) : (digitsCode c L).length = digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [digitsCode, digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl
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
theorem _root_.solution (e : Expr) (k : ℕ) : (compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [compileExpr, Expr.size, iha, ihb]
  | load a ih => simp [compileExpr, Expr.size, ih]
end Light.Compiler
