-- Prove2me | solution 1 for Light.Stmt.width_call_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:07.241425+00:00
-- url     : https://prove2.me/submissions/f092a49e-54b2-4bbd-bdd8-2e283b121b74

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_Light_maxOf_le_iff
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
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [Stmt.width, max_le_iff, maxOf_le_iff, Nat.succ_le_iff]
end Stmt
end Light
