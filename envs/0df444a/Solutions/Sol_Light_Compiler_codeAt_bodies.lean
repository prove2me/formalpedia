-- Prove2me | solution 1 for Light.Compiler.codeAt_bodies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:17.807489+00:00
-- url     : https://prove2.me/submissions/b2931aa5-fb93-4df8-995d-b0d408896d57

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_Light_Compiler_length_compileStmt
import Theorems.Thm_Light_Compiler_length_epilogue
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
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
theorem _root_.solution {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    solution G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, length_compileStmt, length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)
end Light.Compiler
