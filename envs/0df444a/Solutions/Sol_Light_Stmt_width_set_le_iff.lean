-- Prove2me | solution 1 for Light.Stmt.width_set_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:20.859205+00:00
-- url     : https://prove2.me/submissions/45566df0-7031-411c-929d-8e72a3022690

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
theorem _root_.solution : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff
end Stmt
end Light
