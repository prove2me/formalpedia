-- Prove2me | solution 1 for Light.Compiler.cStack_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:00.311099+00:00
-- url     : https://prove2.me/submissions/14aa06c9-15a1-4a1f-bc08-b11c9c983ee7

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by
  simp only [cStack]
  push_cast
  ring
end Light.Compiler
