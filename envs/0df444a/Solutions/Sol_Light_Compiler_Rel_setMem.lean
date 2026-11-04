-- Prove2me | solution 1 for Light.Compiler.Rel.setMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:11.144252+00:00
-- url     : https://prove2.me/submissions/28325179-c198-44f9-86ad-5cc7edcbf928

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_Light_Compiler_Rel_of_agreeOutside
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}
namespace Light.Compiler
namespace Rel
theorem _root_.solution (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  
  have hnonneg : 0 ≤ a := ha.1
  refine
    R.of_agreeOutside ((AgreeOutside.refl { a } m).update rfl _)
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (by
        ((repeat
              (first
                | rw [_root_.Function.update_self]
                |
                  rw [_root_.Function.update_of_ne
                      (by
                        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                                _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                                _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                                _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                                _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
          exact R.fp))
      (fun x hx => by
        ((repeat
              (first
                | rw [_root_.Function.update_self]
                |
                  rw [_root_.Function.update_of_ne
                      (by
                        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                                _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                                _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                                _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                                _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
          exact R.loc x hx))
      fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · simp [Int.toNat_of_nonneg hnonneg]
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])
end Rel
end Light.Compiler
