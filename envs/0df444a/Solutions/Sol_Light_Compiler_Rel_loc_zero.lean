-- Prove2me | solution 1 for Light.Compiler.Rel.loc_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:10.13845+00:00
-- url     : https://prove2.me/submissions/df0101b0-1349-4b43-b626-3bf836f69cf0

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}
namespace Light.Compiler
namespace Rel
theorem _root_.solution (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) :=
  R.loc 0 hF
end Rel
end Light.Compiler
