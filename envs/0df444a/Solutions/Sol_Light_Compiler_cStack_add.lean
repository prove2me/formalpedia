-- Prove2me | solution 1 for Light.Compiler.cStack_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:01.705338+00:00
-- url     : https://prove2.me/submissions/784e33d3-dfe8-4ea8-8da4-25fd93e38b83

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
theorem _root_.solution (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by
  simp only [cStack]
  push_cast
  ring
end Light.Compiler
