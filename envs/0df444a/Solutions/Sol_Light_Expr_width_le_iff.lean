-- Prove2me | solution 1 for Light.Expr.width_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:17.510033+00:00
-- url     : https://prove2.me/submissions/012aae0c-0a6f-41c2-b14a-22fdd1318043

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode

set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
namespace Light
namespace Expr
theorem _root_.solution : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff
end Expr
end Light
