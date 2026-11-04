-- Prove2me | solution 1 for Light.Compiler.straight_argsCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:29.926299+00:00
-- url     : https://prove2.me/submissions/5d1ca82b-97e8-47be-9749-d065b83ff8fa

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Theorems.Thm_Light_Compiler_straight_compileExpr
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  | [], _ => by simp [argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨straight_compileExpr e k, solution es (k + 1)⟩
end Light.Compiler
