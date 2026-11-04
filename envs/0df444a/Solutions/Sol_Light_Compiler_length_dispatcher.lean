-- Prove2me | solution 1 for Light.Compiler.length_dispatcher
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:51.203197+00:00
-- url     : https://prove2.me/submissions/2e8205cf-82ba-4412-a483-12b54e1845ef

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}
namespace Light.Compiler
theorem _root_.solution (n : ℕ) : (dispatcher n).length = 2 * n := by
  simp [dispatcher, List.length_flatMap, Nat.mul_comm]
end Light.Compiler
