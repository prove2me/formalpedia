-- Prove2me | solution 1 for Light.Compiler.straight_compileExpr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:08.734813+00:00
-- url     : https://prove2.me/submissions/249ff6c2-b4d5-414c-8396-588963707b02

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {F : ℕ}
private theorem straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ digitsCode c L, Straight i
  | [] => by simp [digitsCode, Straight]
  | d :: L => by
    have := straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [digitsCode, hd, Straight, or_imp, forall_and] using this
private theorem straight_instr (o : Op) (i j k : ℤ) : Straight (o.instr i j k) := by
  cases o <;> trivial
variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  | .const _, _ => straight_digitsCode _ _
  | .var _, _ => by simp [compileExpr, Straight]
  | .op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨solution a k, solution b (k + 1)⟩, by simp [straight_instr]⟩
  | .load a, k => List.forall_mem_append.2 ⟨solution a k, by simp [Straight]⟩
end Light.Compiler
