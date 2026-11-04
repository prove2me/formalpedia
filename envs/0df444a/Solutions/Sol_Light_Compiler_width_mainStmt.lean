-- Prove2me | solution 1 for Light.Compiler.width_mainStmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:34.760697+00:00
-- url     : https://prove2.me/submissions/1236496a-f4f0-4233-99dc-f7bfe4341e7a

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (p0 : ℕ) : (mainStmt p0).width = 3 := rfl
end Light.Compiler
