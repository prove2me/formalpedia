-- Prove2me | solution 1 for Light.Compiler.Sizes.inRange_addr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:03.486816+00:00
-- url     : https://prove2.me/submissions/ac1839a8-fd09-4c6b-ab51-343d674475f1

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
namespace Sizes
theorem _root_.solution (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]
end Sizes
end Light.Compiler
