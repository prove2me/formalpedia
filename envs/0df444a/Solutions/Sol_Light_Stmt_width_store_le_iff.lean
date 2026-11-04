-- Prove2me | solution 1 for Light.Stmt.width_store_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:00.412933+00:00
-- url     : https://prove2.me/submissions/3682dc7f-ff41-4e53-b54e-8e39d6c8207e

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
theorem _root_.solution : (Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff
end Stmt
end Light
