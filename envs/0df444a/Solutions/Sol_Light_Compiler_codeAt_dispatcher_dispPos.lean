-- Prove2me | solution 1 for Light.Compiler.codeAt_dispatcher_dispPos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:15.518196+00:00
-- url     : https://prove2.me/submissions/7c3c3eb5-9a97-4c17-b142-3fe31abc5dc3

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_Light_Compiler_size_mainStmt
import Theorems.Thm_Light_Compiler_length_compileStmt
import Theorems.Thm_Light_Compiler_length_epilogue
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_codeAt_self
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
private theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl
private theorem length_bodiesCode (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), pos + (bodiesCode G bs pos).length = endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := length_bodiesCode G bs (pos + b.size G.F + epilogueSize)
    simp only [bodiesCode, endPos, List.length_append, length_compileStmt, length_epilogue]
    omega
section parts
variable (P : Program) (p0 : ℕ) (dec : Bool)
private theorem length_through_mainCode :
    (headCode P dec ++ mainCode P p0 dec).length = firstBody (frameSize P) dec := by
  simp only [headCode, headStraight, mainCode, List.length_append, length_compileStmt,
    size_mainStmt, length_tailCode, firstBody, tailPos, mainPos, codeLayout, List.length_cons,
    List.length_nil]
  omega
private theorem length_through_bodiesCode :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)).length = dispPos P dec := by
  rw [List.length_append, length_through_mainCode]
  exact length_bodiesCode (codeLayout P dec) P _
end parts
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)
namespace Light.Compiler
theorem _root_.solution :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) :=
  (codeAt_self _).left.right.cast_pos (by rw [length_through_bodiesCode, Nat.zero_add])
end Light.Compiler
