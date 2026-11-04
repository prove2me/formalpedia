-- Prove2me | solution 1 for Light.Cond.width_lt_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:18.619753+00:00
-- url     : https://prove2.me/submissions/3ee30c71-3c09-4c96-9a12-98dbbdd70b63

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode

set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
namespace Light
namespace Cond
theorem _root_.solution : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff
end Cond
end Light
