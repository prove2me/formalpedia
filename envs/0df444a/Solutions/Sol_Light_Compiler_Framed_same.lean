-- Prove2me | solution 1 for Light.Compiler.Framed.same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:48.37375+00:00
-- url     : https://prove2.me/submissions/d255134a-c7a5-4f58-98ac-428311bcff41

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_Light_Compiler_Rel_same

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}
namespace Light.Compiler
namespace Framed
theorem _root_.solution (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩
end Framed
end Light.Compiler
