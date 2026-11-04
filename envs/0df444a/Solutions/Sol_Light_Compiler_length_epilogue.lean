-- Prove2me | solution 1 for Light.Compiler.length_epilogue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:44.671885+00:00
-- url     : https://prove2.me/submissions/b5fcb34d-bef5-4f2e-b2a2-72656d59faad

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode

set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (G : CodeLayout) : (epilogue G).length = epilogueSize := rfl
end Light.Compiler
