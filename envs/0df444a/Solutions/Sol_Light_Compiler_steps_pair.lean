-- Prove2me | solution 1 for Light.Compiler.steps_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:15.957597+00:00
-- url     : https://prove2.me/submissions/4da48303-6058-45ba-94c0-c11156d60e80

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Theorems.Thm_Light_Compiler_Framed_same
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Rel_same
import Theorems.Thm_Light_Compiler_effects_compileExpr_of_width
import Theorems.Thm_Light_Compiler_length_compileExpr
import Theorems.Thm_Light_Compiler_straight_compileExpr
import Theorems.Thm_Light_Compiler_temps_subset_scratch
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_steps_straight
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ} {m : ℤ → BitVec W} {a b : Expr}
namespace Light.Compiler
theorem _root_.solution (I : Framed Z σ q m) (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest))
    (hwa : a.width ≤ Z.F) (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m',
      Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
        m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧ AgreeOutside (Scratch Z.F) m m' :=
  by
  obtain ⟨va, Aa⟩ := effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have Aa' := Aa.mono temps_subset_scratch
  obtain ⟨vb, Ab⟩ := effects_compileExpr_of_width (I.same Aa') b 1 hwb hsb (by omega)
  have run :=
    steps_straight _ pos m hcode.left (List.forall_mem_append.2 ⟨straight_compileExpr a 0, straight_compileExpr b 1⟩)
  rw [List.length_append, length_compileExpr, length_compileExpr, effects_append] at run
  exact
    ⟨_, run,
      Ab.read
        (by
          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                  _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                  _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                  _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                  _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                  _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                  _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                  _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega))
        va,
      vb, Aa'.trans (Ab.mono temps_subset_scratch)⟩
end Light.Compiler
