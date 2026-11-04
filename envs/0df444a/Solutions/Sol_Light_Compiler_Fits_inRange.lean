-- Prove2me | solution 1 for Light.Compiler.Fits.inRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:10.744279+00:00
-- url     : https://prove2.me/submissions/c21044ce-c307-46bf-b726-d2783e400e90

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_inRange_of_abs_le


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
namespace Light.Compiler
namespace Fits
theorem _root_.solution {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v :=
  inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h
end Fits
end Light.Compiler
