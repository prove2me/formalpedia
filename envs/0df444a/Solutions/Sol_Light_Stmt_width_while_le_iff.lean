-- Prove2me | solution 1 for Light.Stmt.width_while_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:05.762088+00:00
-- url     : https://prove2.me/submissions/752309f8-3a5f-45da-bdf7-c8ef4b1b59f3

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode

set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
namespace Light
namespace Stmt
theorem _root_.solution : (Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff
end Stmt
end Light
