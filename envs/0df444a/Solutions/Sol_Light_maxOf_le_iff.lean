-- Prove2me | solution 1 for Light.maxOf_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:00.424395+00:00
-- url     : https://prove2.me/submissions/43416c9c-5d27-4636-8ec2-634735145a92

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
theorem _root_.solution {α : Type} {f : α → ℕ} {l : List α} : maxOf f l ≤ F ↔ ∀ y ∈ l, f y ≤ F := by
  induction l <;> simp [maxOf, *]
end Light
