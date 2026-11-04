-- Prove2me | solution 1 for Light.Compiler.two_mul_frameSize_add_le_dispPos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:52.421503+00:00
-- url     : https://prove2.me/submissions/83638233-6b26-4977-9c9f-5f05cde715a6

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_Light_Compiler_size_mainStmt
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
private theorem le_endPos (F : ℕ) : ∀ (bs : List Stmt) (pos : ℕ), pos ≤ endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (le_endPos F bs (pos + b.size F + epilogueSize))
private theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl
section parts
variable (P : Program) (p0 : ℕ) (dec : Bool)
end parts
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by
  have : firstBody (frameSize P) dec ≤ dispPos P dec := le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [firstBody, tailPos, mainPos, size_mainStmt, length_tailCode] at this
  omega
end Light.Compiler
