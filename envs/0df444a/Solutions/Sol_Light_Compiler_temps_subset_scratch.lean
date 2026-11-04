-- Prove2me | solution 1 for Light.Compiler.temps_subset_scratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:05.070863+00:00
-- url     : https://prove2.me/submissions/c720daad-4e12-4ab5-be92-e31430526ec2

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
namespace Light.Compiler
theorem _root_.solution {k : ℕ} : Temps k F ⊆ Scratch F := by
  (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
          _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
          _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
          _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
          _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
          _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
          _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
          _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
          _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
          _root_.false_or, _root_.or_false] <;>
        intros <;>
      omega)
end Light.Compiler
