-- Prove2me | solution 1 for Light.Compiler.mem_writable_of_addr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:10.684064+00:00
-- url     : https://prove2.me/submissions/08b72bee-8bb8-4f1f-a407-466c056a8f73

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q :=
  Set.mem_union_right _ h
end Light.Compiler
