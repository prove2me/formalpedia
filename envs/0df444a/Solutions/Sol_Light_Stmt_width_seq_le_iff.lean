-- Prove2me | solution 1 for Light.Stmt.width_seq_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:01.856331+00:00
-- url     : https://prove2.me/submissions/c85cd24a-9bfd-4e55-8803-7d34352d947e

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
theorem _root_.solution : (Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff
end Stmt
end Light
