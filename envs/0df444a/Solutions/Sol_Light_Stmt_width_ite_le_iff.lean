-- Prove2me | solution 1 for Light.Stmt.width_ite_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:04.466674+00:00
-- url     : https://prove2.me/submissions/dfd90046-33f5-4653-93a0-dfa0a04e8e35

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
namespace Light
namespace Stmt
theorem _root_.solution :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [Stmt.width, max_le_iff]
end Stmt
end Light
