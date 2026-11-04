-- Prove2me | solution 1 for Light.Compiler.Sizes.inRange_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:05.021434+00:00
-- url     : https://prove2.me/submissions/97eec26f-6baa-4465-a4a7-a27cf160220e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
namespace Sizes
theorem _root_.solution (Z : Sizes W) : InRange W (-1) := by
  have hN : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]
end Sizes
end Light.Compiler
