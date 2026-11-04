-- Prove2me | solution 1 for Light.Compiler.Rel.of_agreeOutside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:23.390169+00:00
-- url     : https://prove2.me/submissions/4b0e208c-ce84-4446-a4c7-f18308b8ca3d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}
namespace Light.Compiler
namespace Rel
theorem _root_.solution {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m') (hs : s ⊆ (Constants Z.disp)ᶜ)
    (hfp : m' cFP = wd W (cStack q')) (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' :=
  by
  have keep {a : ℤ} (ha : a ∈ Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact
    { one :=
        (keep
              (by
                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                        _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                        _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                        _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                        _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
                        _root_.or_false] <;>
                      intros <;>
                    omega))).trans
          R.one
      zero :=
        (keep
              (by
                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                        _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                        _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                        _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                        _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
                        _root_.or_false] <;>
                      intros <;>
                    omega))).trans
          R.zero
      neg :=
        (keep
              (by
                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                        _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                        _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                        _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                        _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
                        _root_.or_false] <;>
                      intros <;>
                    omega))).trans
          R.neg
      pool := fun n hn =>
        (keep
              (by
                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                        _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                        _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                        _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                        _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
                        _root_.or_false] <;>
                      intros <;>
                    omega))).trans
          (R.pool n hn)
      fp := hfp
      loc := hloc
      mem := hmem }
end Rel
end Light.Compiler
