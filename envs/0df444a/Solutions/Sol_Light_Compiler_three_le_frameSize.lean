-- Prove2me | solution 1 for Light.Compiler.three_le_frameSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:25.108451+00:00
-- url     : https://prove2.me/submissions/1727ae27-4d90-49db-bc80-8dcfce2e2267

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution (P : Program) : 3 ≤ frameSize P := le_max_left _ _
end Light.Compiler
