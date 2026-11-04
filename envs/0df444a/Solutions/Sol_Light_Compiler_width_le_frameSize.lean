-- Prove2me | solution 1 for Light.Compiler.width_le_frameSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:33.560959+00:00
-- url     : https://prove2.me/submissions/f6b3ed8b-9683-444b-932d-634b105e9855

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Theorems.Thm_Light_maxOf_le_iff
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
theorem _root_.solution {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P :=
  (maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)
end Light.Compiler
