-- Prove2me | solution 1 for Light.Cond.width_eq_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:19.75175+00:00
-- url     : https://prove2.me/submissions/eac6b705-85aa-4e73-a69b-3efb14a7751a

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
theorem _root_.solution : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff
end Cond
end Light
