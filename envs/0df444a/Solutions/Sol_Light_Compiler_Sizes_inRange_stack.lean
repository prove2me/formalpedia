-- Prove2me | solution 1 for Light.Compiler.Sizes.inRange_stack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:32.647164+00:00
-- url     : https://prove2.me/submissions/346aa2ec-c47a-4272-9bc7-72d15df42d75

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
namespace Sizes
theorem _root_.solution (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [cStack] <;> linarith [Z.fits.stack]
end Sizes
end Light.Compiler
